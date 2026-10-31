/*
 * elk-lean C helpers for org.eclipse.elk.core.
 *
 * Lean's `Float.toString` prints with a fixed number of decimals, which is neither round-trip
 * safe nor compatible with the reference JSON output of elkjs / elk-rs.
 *   - `elk_float_to_json` prints a finite double exactly like the elk-rs oracle's serde_json
 *     1.0.149, i.e. zmij 1.0.19 `Buffer::format_finite`: `12.0`, `0.1`, `1e+21`, `3e-6`.
 *   - `elk_float_to_shortest` uses the same shortest round-trip digits with ryu-style positive
 *     exponents (`1e21`) and `NaN` / `inf` / `-inf` for non-finite values.
 * `elk_strtod` is a correctly rounded decimal-to-double conversion.
 *
 * ---------------------------------------------------------------------------------------------
 * The double-to-string conversion (`elk_zmij_*`) is a C port of the f64 path of the Rust crate
 * zmij 1.0.19 by David Tolnay (https://github.com/dtolnay/zmij), itself a line-by-line port of
 * Victor Zverovich's C++ implementation (https://github.com/vitaut/zmij), an algorithm based on
 * Schubfach (Raffaello Giulietti) and yy_double (Yaoyuan Guo). zmij is distributed under the
 * MIT license:
 *
 *   Permission is hereby granted, free of charge, to any person obtaining a copy of this
 *   software and associated documentation files (the "Software"), to deal in the Software
 *   without restriction, including without limitation the rights to use, copy, modify, merge,
 *   publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons
 *   to whom the Software is furnished to do so, subject to the following conditions:
 *
 *   The above copyright notice and this permission notice shall be included in all copies or
 *   substantial portions of the Software.
 *
 *   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED,
 *   INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR
 *   PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE
 *   FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR
 *   OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 *   DEALINGS IN THE SOFTWARE.
 *
 * Differences from the Rust source, none of which changes the output: only the f64 path is
 * ported; the SIMD significand writers are replaced by the portable `to_bcd8` path; the
 * exponent-shift table is computed inline (`do_compute_exp_shift`, which is how the table is
 * built); `POW10_SIGNIFICANDS` (built by a const fn in Rust) is the generated table below; the
 * exponent digits are written with plain stores. Without `unsigned __int128` a portable 64x64 ->
 * 128-bit multiplication is used (define `ELK_ZMIJ_NO_INT128` to force it).
 * ---------------------------------------------------------------------------------------------
 */
#include <lean/lean.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ---- zmij: 128-bit arithmetic ------------------------------------------------------------ */

/* zmij `uint128`. */
typedef struct {
    uint64_t hi;
    uint64_t lo;
} elk_zmij_u128;

#if defined(__SIZEOF_INT128__) && !defined(ELK_ZMIJ_NO_INT128)
__extension__ typedef unsigned __int128 elk_zmij_native_u128;

/* zmij `umul128`: the 128-bit product of x and y; returns the low half, stores the high half. */
static inline uint64_t elk_zmij_umul128(uint64_t x, uint64_t y, uint64_t *hi) {
    elk_zmij_native_u128 p = (elk_zmij_native_u128)x * y;
    *hi = (uint64_t)(p >> 64);
    return (uint64_t)p;
}
#else
static inline uint64_t elk_zmij_umul128(uint64_t x, uint64_t y, uint64_t *hi) {
    uint64_t x_lo = (uint32_t)x, x_hi = x >> 32, y_lo = (uint32_t)y, y_hi = y >> 32;
    uint64_t ll = x_lo * y_lo, lh = x_lo * y_hi, hl = x_hi * y_lo, hh = x_hi * y_hi;
    uint64_t mid = (ll >> 32) + (uint32_t)lh + (uint32_t)hl;
    *hi = hh + (lh >> 32) + (hl >> 32) + (mid >> 32);
    return (mid << 32) | (uint32_t)ll;
}
#endif

/* zmij `umul128_hi64`. */
static inline uint64_t elk_zmij_umul128_hi64(uint64_t x, uint64_t y) {
    uint64_t hi;
    (void)elk_zmij_umul128(x, y, &hi);
    return hi;
}

/* zmij `umul192_hi128`: high 128 bits of (x_hi * 2^64 + x_lo) * y, low product truncated. */
static inline elk_zmij_u128 elk_zmij_umul192_hi128(uint64_t x_hi, uint64_t x_lo, uint64_t y) {
    uint64_t p_hi;
    uint64_t p_lo = elk_zmij_umul128(x_hi, y, &p_hi);
    uint64_t lo = p_lo + elk_zmij_umul128_hi64(x_lo, y);
    elk_zmij_u128 r = {p_hi + (uint64_t)(lo < p_lo), lo};
    return r;
}

/* zmij `umulhi_inexact_to_odd` (64-bit): high 64 bits of the product, rounded to odd. */
static inline uint64_t elk_zmij_umulhi_inexact_to_odd(uint64_t x_hi, uint64_t x_lo, uint64_t y) {
    elk_zmij_u128 p = elk_zmij_umul192_hi128(x_hi, x_lo, y);
    return p.hi | (uint64_t)((p.lo >> 1) != 0);
}

/* `x >> n` on i32 with Rust's arithmetic (flooring) semantics, without relying on the
 * implementation-defined right shift of negative values in C. */
static inline int32_t elk_zmij_asr(int32_t x, int n) {
    return x >= 0 ? x >> n : ~(~x >> n);
}

/* ---- zmij: powers of ten ------------------------------------------------------------------ */

/* zmij `POW10_SIGNIFICANDS`: 128-bit significands {hi, lo} of 10^k rounded down, for
 * k = -292..324 (index k + 292). Generated with zmij's 192-bit method by Dougall Johnson:
 *   current = {w0: 0xe000000000000000, w1: 0x25e8e89c13bb0f7a, w2: 0xff77b1fcbebcdc4f}
 *   per entry: emit {w2, w1}; multiply the 192-bit current by ten = 0xa000000000000000
 *   (h0 = hi64(w0*ten), h1 = hi64(w1*ten), c0 = h0 + w1*ten, c1 = (c0 < h0) + h1 + w2*ten,
 *   c2 = (c1 < h1) + hi64(w2*ten)) and normalise (shift left by one if bit 63 of c2 is clear). */
static const uint64_t elk_zmij_pow10[617][2] = {
    /* 1e-292 */ {0xff77b1fcbebcdc4f, 0x25e8e89c13bb0f7a}, {0x9faacf3df73609b1, 0x77b191618c54e9ac},
    /* 1e-290 */ {0xc795830d75038c1d, 0xd59df5b9ef6a2417}, {0xf97ae3d0d2446f25, 0x4b0573286b44ad1d},
    /* 1e-288 */ {0x9becce62836ac577, 0x4ee367f9430aec32}, {0xc2e801fb244576d5, 0x229c41f793cda73f},
    /* 1e-286 */ {0xf3a20279ed56d48a, 0x6b43527578c1110f}, {0x9845418c345644d6, 0x830a13896b78aaa9},
    /* 1e-284 */ {0xbe5691ef416bd60c, 0x23cc986bc656d553}, {0xedec366b11c6cb8f, 0x2cbfbe86b7ec8aa8},
    /* 1e-282 */ {0x94b3a202eb1c3f39, 0x7bf7d71432f3d6a9}, {0xb9e08a83a5e34f07, 0xdaf5ccd93fb0cc53},
    /* 1e-280 */ {0xe858ad248f5c22c9, 0xd1b3400f8f9cff68}, {0x91376c36d99995be, 0x23100809b9c21fa1},
    /* 1e-278 */ {0xb58547448ffffb2d, 0xabd40a0c2832a78a}, {0xe2e69915b3fff9f9, 0x16c90c8f323f516c},
    /* 1e-276 */ {0x8dd01fad907ffc3b, 0xae3da7d97f6792e3}, {0xb1442798f49ffb4a, 0x99cd11cfdf41779c},
    /* 1e-274 */ {0xdd95317f31c7fa1d, 0x40405643d711d583}, {0x8a7d3eef7f1cfc52, 0x482835ea666b2572},
    /* 1e-272 */ {0xad1c8eab5ee43b66, 0xda3243650005eecf}, {0xd863b256369d4a40, 0x90bed43e40076a82},
    /* 1e-270 */ {0x873e4f75e2224e68, 0x5a7744a6e804a291}, {0xa90de3535aaae202, 0x711515d0a205cb36},
    /* 1e-268 */ {0xd3515c2831559a83, 0x0d5a5b44ca873e03}, {0x8412d9991ed58091, 0xe858790afe9486c2},
    /* 1e-266 */ {0xa5178fff668ae0b6, 0x626e974dbe39a872}, {0xce5d73ff402d98e3, 0xfb0a3d212dc8128f},
    /* 1e-264 */ {0x80fa687f881c7f8e, 0x7ce66634bc9d0b99}, {0xa139029f6a239f72, 0x1c1fffc1ebc44e80},
    /* 1e-262 */ {0xc987434744ac874e, 0xa327ffb266b56220}, {0xfbe9141915d7a922, 0x4bf1ff9f0062baa8},
    /* 1e-260 */ {0x9d71ac8fada6c9b5, 0x6f773fc3603db4a9}, {0xc4ce17b399107c22, 0xcb550fb4384d21d3},
    /* 1e-258 */ {0xf6019da07f549b2b, 0x7e2a53a146606a48}, {0x99c102844f94e0fb, 0x2eda7444cbfc426d},
    /* 1e-256 */ {0xc0314325637a1939, 0xfa911155fefb5308}, {0xf03d93eebc589f88, 0x793555ab7eba27ca},
    /* 1e-254 */ {0x96267c7535b763b5, 0x4bc1558b2f3458de}, {0xbbb01b9283253ca2, 0x9eb1aaedfb016f16},
    /* 1e-252 */ {0xea9c227723ee8bcb, 0x465e15a979c1cadc}, {0x92a1958a7675175f, 0x0bfacd89ec191ec9},
    /* 1e-250 */ {0xb749faed14125d36, 0xcef980ec671f667b}, {0xe51c79a85916f484, 0x82b7e12780e7401a},
    /* 1e-248 */ {0x8f31cc0937ae58d2, 0xd1b2ecb8b0908810}, {0xb2fe3f0b8599ef07, 0x861fa7e6dcb4aa15},
    /* 1e-246 */ {0xdfbdcece67006ac9, 0x67a791e093e1d49a}, {0x8bd6a141006042bd, 0xe0c8bb2c5c6d24e0},
    /* 1e-244 */ {0xaecc49914078536d, 0x58fae9f773886e18}, {0xda7f5bf590966848, 0xaf39a475506a899e},
    /* 1e-242 */ {0x888f99797a5e012d, 0x6d8406c952429603}, {0xaab37fd7d8f58178, 0xc8e5087ba6d33b83},
    /* 1e-240 */ {0xd5605fcdcf32e1d6, 0xfb1e4a9a90880a64}, {0x855c3be0a17fcd26, 0x5cf2eea09a55067f},
    /* 1e-238 */ {0xa6b34ad8c9dfc06f, 0xf42faa48c0ea481e}, {0xd0601d8efc57b08b, 0xf13b94daf124da26},
    /* 1e-236 */ {0x823c12795db6ce57, 0x76c53d08d6b70858}, {0xa2cb1717b52481ed, 0x54768c4b0c64ca6e},
    /* 1e-234 */ {0xcb7ddcdda26da268, 0xa9942f5dcf7dfd09}, {0xfe5d54150b090b02, 0xd3f93b35435d7c4c},
    /* 1e-232 */ {0x9efa548d26e5a6e1, 0xc47bc5014a1a6daf}, {0xc6b8e9b0709f109a, 0x359ab6419ca1091b},
    /* 1e-230 */ {0xf867241c8cc6d4c0, 0xc30163d203c94b62}, {0x9b407691d7fc44f8, 0x79e0de63425dcf1d},
    /* 1e-228 */ {0xc21094364dfb5636, 0x985915fc12f542e4}, {0xf294b943e17a2bc4, 0x3e6f5b7b17b2939d},
    /* 1e-226 */ {0x979cf3ca6cec5b5a, 0xa705992ceecf9c42}, {0xbd8430bd08277231, 0x50c6ff782a838353},
    /* 1e-224 */ {0xece53cec4a314ebd, 0xa4f8bf5635246428}, {0x940f4613ae5ed136, 0x871b7795e136be99},
    /* 1e-222 */ {0xb913179899f68584, 0x28e2557b59846e3f}, {0xe757dd7ec07426e5, 0x331aeada2fe589cf},
    /* 1e-220 */ {0x9096ea6f3848984f, 0x3ff0d2c85def7621}, {0xb4bca50b065abe63, 0x0fed077a756b53a9},
    /* 1e-218 */ {0xe1ebce4dc7f16dfb, 0xd3e8495912c62894}, {0x8d3360f09cf6e4bd, 0x64712dd7abbbd95c},
    /* 1e-216 */ {0xb080392cc4349dec, 0xbd8d794d96aacfb3}, {0xdca04777f541c567, 0xecf0d7a0fc5583a0},
    /* 1e-214 */ {0x89e42caaf9491b60, 0xf41686c49db57244}, {0xac5d37d5b79b6239, 0x311c2875c522ced5},
    /* 1e-212 */ {0xd77485cb25823ac7, 0x7d633293366b828b}, {0x86a8d39ef77164bc, 0xae5dff9c02033197},
    /* 1e-210 */ {0xa8530886b54dbdeb, 0xd9f57f830283fdfc}, {0xd267caa862a12d66, 0xd072df63c324fd7b},
    /* 1e-208 */ {0x8380dea93da4bc60, 0x4247cb9e59f71e6d}, {0xa46116538d0deb78, 0x52d9be85f074e608},
    /* 1e-206 */ {0xcd795be870516656, 0x67902e276c921f8b}, {0x806bd9714632dff6, 0x00ba1cd8a3db53b6},
    /* 1e-204 */ {0xa086cfcd97bf97f3, 0x80e8a40eccd228a4}, {0xc8a883c0fdaf7df0, 0x6122cd128006b2cd},
    /* 1e-202 */ {0xfad2a4b13d1b5d6c, 0x796b805720085f81}, {0x9cc3a6eec6311a63, 0xcbe3303674053bb0},
    /* 1e-200 */ {0xc3f490aa77bd60fc, 0xbedbfc4411068a9c}, {0xf4f1b4d515acb93b, 0xee92fb5515482d44},
    /* 1e-198 */ {0x991711052d8bf3c5, 0x751bdd152d4d1c4a}, {0xbf5cd54678eef0b6, 0xd262d45a78a0635d},
    /* 1e-196 */ {0xef340a98172aace4, 0x86fb897116c87c34}, {0x9580869f0e7aac0e, 0xd45d35e6ae3d4da0},
    /* 1e-194 */ {0xbae0a846d2195712, 0x8974836059cca109}, {0xe998d258869facd7, 0x2bd1a438703fc94b},
    /* 1e-192 */ {0x91ff83775423cc06, 0x7b6306a34627ddcf}, {0xb67f6455292cbf08, 0x1a3bc84c17b1d542},
    /* 1e-190 */ {0xe41f3d6a7377eeca, 0x20caba5f1d9e4a93}, {0x8e938662882af53e, 0x547eb47b7282ee9c},
    /* 1e-188 */ {0xb23867fb2a35b28d, 0xe99e619a4f23aa43}, {0xdec681f9f4c31f31, 0x6405fa00e2ec94d4},
    /* 1e-186 */ {0x8b3c113c38f9f37e, 0xde83bc408dd3dd04}, {0xae0b158b4738705e, 0x9624ab50b148d445},
    /* 1e-184 */ {0xd98ddaee19068c76, 0x3badd624dd9b0957}, {0x87f8a8d4cfa417c9, 0xe54ca5d70a80e5d6},
    /* 1e-182 */ {0xa9f6d30a038d1dbc, 0x5e9fcf4ccd211f4c}, {0xd47487cc8470652b, 0x7647c3200069671f},
    /* 1e-180 */ {0x84c8d4dfd2c63f3b, 0x29ecd9f40041e073}, {0xa5fb0a17c777cf09, 0xf468107100525890},
    /* 1e-178 */ {0xcf79cc9db955c2cc, 0x7182148d4066eeb4}, {0x81ac1fe293d599bf, 0xc6f14cd848405530},
    /* 1e-176 */ {0xa21727db38cb002f, 0xb8ada00e5a506a7c}, {0xca9cf1d206fdc03b, 0xa6d90811f0e4851c},
    /* 1e-174 */ {0xfd442e4688bd304a, 0x908f4a166d1da663}, {0x9e4a9cec15763e2e, 0x9a598e4e043287fe},
    /* 1e-172 */ {0xc5dd44271ad3cdba, 0x40eff1e1853f29fd}, {0xf7549530e188c128, 0xd12bee59e68ef47c},
    /* 1e-170 */ {0x9a94dd3e8cf578b9, 0x82bb74f8301958ce}, {0xc13a148e3032d6e7, 0xe36a52363c1faf01},
    /* 1e-168 */ {0xf18899b1bc3f8ca1, 0xdc44e6c3cb279ac1}, {0x96f5600f15a7b7e5, 0x29ab103a5ef8c0b9},
    /* 1e-166 */ {0xbcb2b812db11a5de, 0x7415d448f6b6f0e7}, {0xebdf661791d60f56, 0x111b495b3464ad21},
    /* 1e-164 */ {0x936b9fcebb25c995, 0xcab10dd900beec34}, {0xb84687c269ef3bfb, 0x3d5d514f40eea742},
    /* 1e-162 */ {0xe65829b3046b0afa, 0x0cb4a5a3112a5112}, {0x8ff71a0fe2c2e6dc, 0x47f0e785eaba72ab},
    /* 1e-160 */ {0xb3f4e093db73a093, 0x59ed216765690f56}, {0xe0f218b8d25088b8, 0x306869c13ec3532c},
    /* 1e-158 */ {0x8c974f7383725573, 0x1e414218c73a13fb}, {0xafbd2350644eeacf, 0xe5d1929ef90898fa},
    /* 1e-156 */ {0xdbac6c247d62a583, 0xdf45f746b74abf39}, {0x894bc396ce5da772, 0x6b8bba8c328eb783},
    /* 1e-154 */ {0xab9eb47c81f5114f, 0x066ea92f3f326564}, {0xd686619ba27255a2, 0xc80a537b0efefebd},
    /* 1e-152 */ {0x8613fd0145877585, 0xbd06742ce95f5f36}, {0xa798fc4196e952e7, 0x2c48113823b73704},
    /* 1e-150 */ {0xd17f3b51fca3a7a0, 0xf75a15862ca504c5}, {0x82ef85133de648c4, 0x9a984d73dbe722fb},
    /* 1e-148 */ {0xa3ab66580d5fdaf5, 0xc13e60d0d2e0ebba}, {0xcc963fee10b7d1b3, 0x318df905079926a8},
    /* 1e-146 */ {0xffbbcfe994e5c61f, 0xfdf17746497f7052}, {0x9fd561f1fd0f9bd3, 0xfeb6ea8bedefa633},
    /* 1e-144 */ {0xc7caba6e7c5382c8, 0xfe64a52ee96b8fc0}, {0xf9bd690a1b68637b, 0x3dfdce7aa3c673b0},
    /* 1e-142 */ {0x9c1661a651213e2d, 0x06bea10ca65c084e}, {0xc31bfa0fe5698db8, 0x486e494fcff30a62},
    /* 1e-140 */ {0xf3e2f893dec3f126, 0x5a89dba3c3efccfa}, {0x986ddb5c6b3a76b7, 0xf89629465a75e01c},
    /* 1e-138 */ {0xbe89523386091465, 0xf6bbb397f1135823}, {0xee2ba6c0678b597f, 0x746aa07ded582e2c},
    /* 1e-136 */ {0x94db483840b717ef, 0xa8c2a44eb4571cdc}, {0xba121a4650e4ddeb, 0x92f34d62616ce413},
    /* 1e-134 */ {0xe896a0d7e51e1566, 0x77b020baf9c81d17}, {0x915e2486ef32cd60, 0x0ace1474dc1d122e},
    /* 1e-132 */ {0xb5b5ada8aaff80b8, 0x0d819992132456ba}, {0xe3231912d5bf60e6, 0x10e1fff697ed6c69},
    /* 1e-130 */ {0x8df5efabc5979c8f, 0xca8d3ffa1ef463c1}, {0xb1736b96b6fd83b3, 0xbd308ff8a6b17cb2},
    /* 1e-128 */ {0xddd0467c64bce4a0, 0xac7cb3f6d05ddbde}, {0x8aa22c0dbef60ee4, 0x6bcdf07a423aa96b},
    /* 1e-126 */ {0xad4ab7112eb3929d, 0x86c16c98d2c953c6}, {0xd89d64d57a607744, 0xe871c7bf077ba8b7},
    /* 1e-124 */ {0x87625f056c7c4a8b, 0x11471cd764ad4972}, {0xa93af6c6c79b5d2d, 0xd598e40d3dd89bcf},
    /* 1e-122 */ {0xd389b47879823479, 0x4aff1d108d4ec2c3}, {0x843610cb4bf160cb, 0xcedf722a585139ba},
    /* 1e-120 */ {0xa54394fe1eedb8fe, 0xc2974eb4ee658828}, {0xce947a3da6a9273e, 0x733d226229feea32},
    /* 1e-118 */ {0x811ccc668829b887, 0x0806357d5a3f525f}, {0xa163ff802a3426a8, 0xca07c2dcb0cf26f7},
    /* 1e-116 */ {0xc9bcff6034c13052, 0xfc89b393dd02f0b5}, {0xfc2c3f3841f17c67, 0xbbac2078d443ace2},
    /* 1e-114 */ {0x9d9ba7832936edc0, 0xd54b944b84aa4c0d}, {0xc5029163f384a931, 0x0a9e795e65d4df11},
    /* 1e-112 */ {0xf64335bcf065d37d, 0x4d4617b5ff4a16d5}, {0x99ea0196163fa42e, 0x504bced1bf8e4e45},
    /* 1e-110 */ {0xc06481fb9bcf8d39, 0xe45ec2862f71e1d6}, {0xf07da27a82c37088, 0x5d767327bb4e5a4c},
    /* 1e-108 */ {0x964e858c91ba2655, 0x3a6a07f8d510f86f}, {0xbbe226efb628afea, 0x890489f70a55368b},
    /* 1e-106 */ {0xeadab0aba3b2dbe5, 0x2b45ac74ccea842e}, {0x92c8ae6b464fc96f, 0x3b0b8bc90012929d},
    /* 1e-104 */ {0xb77ada0617e3bbcb, 0x09ce6ebb40173744}, {0xe55990879ddcaabd, 0xcc420a6a101d0515},
    /* 1e-102 */ {0x8f57fa54c2a9eab6, 0x9fa946824a12232d}, {0xb32df8e9f3546564, 0x47939822dc96abf9},
    /* 1e-100 */ {0xdff9772470297ebd, 0x59787e2b93bc56f7}, {0x8bfbea76c619ef36, 0x57eb4edb3c55b65a},
    /* 1e-98 */ {0xaefae51477a06b03, 0xede622920b6b23f1}, {0xdab99e59958885c4, 0xe95fab368e45eced},
    /* 1e-96 */ {0x88b402f7fd75539b, 0x11dbcb0218ebb414}, {0xaae103b5fcd2a881, 0xd652bdc29f26a119},
    /* 1e-94 */ {0xd59944a37c0752a2, 0x4be76d3346f0495f}, {0x857fcae62d8493a5, 0x6f70a4400c562ddb},
    /* 1e-92 */ {0xa6dfbd9fb8e5b88e, 0xcb4ccd500f6bb952}, {0xd097ad07a71f26b2, 0x7e2000a41346a7a7},
    /* 1e-90 */ {0x825ecc24c873782f, 0x8ed400668c0c28c8}, {0xa2f67f2dfa90563b, 0x728900802f0f32fa},
    /* 1e-88 */ {0xcbb41ef979346bca, 0x4f2b40a03ad2ffb9}, {0xfea126b7d78186bc, 0xe2f610c84987bfa8},
    /* 1e-86 */ {0x9f24b832e6b0f436, 0x0dd9ca7d2df4d7c9}, {0xc6ede63fa05d3143, 0x91503d1c79720dbb},
    /* 1e-84 */ {0xf8a95fcf88747d94, 0x75a44c6397ce912a}, {0x9b69dbe1b548ce7c, 0xc986afbe3ee11aba},
    /* 1e-82 */ {0xc24452da229b021b, 0xfbe85badce996168}, {0xf2d56790ab41c2a2, 0xfae27299423fb9c3},
    /* 1e-80 */ {0x97c560ba6b0919a5, 0xdccd879fc967d41a}, {0xbdb6b8e905cb600f, 0x5400e987bbc1c920},
    /* 1e-78 */ {0xed246723473e3813, 0x290123e9aab23b68}, {0x9436c0760c86e30b, 0xf9a0b6720aaf6521},
    /* 1e-76 */ {0xb94470938fa89bce, 0xf808e40e8d5b3e69}, {0xe7958cb87392c2c2, 0xb60b1d1230b20e04},
    /* 1e-74 */ {0x90bd77f3483bb9b9, 0xb1c6f22b5e6f48c2}, {0xb4ecd5f01a4aa828, 0x1e38aeb6360b1af3},
    /* 1e-72 */ {0xe2280b6c20dd5232, 0x25c6da63c38de1b0}, {0x8d590723948a535f, 0x579c487e5a38ad0e},
    /* 1e-70 */ {0xb0af48ec79ace837, 0x2d835a9df0c6d851}, {0xdcdb1b2798182244, 0xf8e431456cf88e65},
    /* 1e-68 */ {0x8a08f0f8bf0f156b, 0x1b8e9ecb641b58ff}, {0xac8b2d36eed2dac5, 0xe272467e3d222f3f},
    /* 1e-66 */ {0xd7adf884aa879177, 0x5b0ed81dcc6abb0f}, {0x86ccbb52ea94baea, 0x98e947129fc2b4e9},
    /* 1e-64 */ {0xa87fea27a539e9a5, 0x3f2398d747b36224}, {0xd29fe4b18e88640e, 0x8eec7f0d19a03aad},
    /* 1e-62 */ {0x83a3eeeef9153e89, 0x1953cf68300424ac}, {0xa48ceaaab75a8e2b, 0x5fa8c3423c052dd7},
    /* 1e-60 */ {0xcdb02555653131b6, 0x3792f412cb06794d}, {0x808e17555f3ebf11, 0xe2bbd88bbee40bd0},
    /* 1e-58 */ {0xa0b19d2ab70e6ed6, 0x5b6aceaeae9d0ec4}, {0xc8de047564d20a8b, 0xf245825a5a445275},
    /* 1e-56 */ {0xfb158592be068d2e, 0xeed6e2f0f0d56712}, {0x9ced737bb6c4183d, 0x55464dd69685606b},
    /* 1e-54 */ {0xc428d05aa4751e4c, 0xaa97e14c3c26b886}, {0xf53304714d9265df, 0xd53dd99f4b3066a8},
    /* 1e-52 */ {0x993fe2c6d07b7fab, 0xe546a8038efe4029}, {0xbf8fdb78849a5f96, 0xde98520472bdd033},
    /* 1e-50 */ {0xef73d256a5c0f77c, 0x963e66858f6d4440}, {0x95a8637627989aad, 0xdde7001379a44aa8},
    /* 1e-48 */ {0xbb127c53b17ec159, 0x5560c018580d5d52}, {0xe9d71b689dde71af, 0xaab8f01e6e10b4a6},
    /* 1e-46 */ {0x9226712162ab070d, 0xcab3961304ca70e8}, {0xb6b00d69bb55c8d1, 0x3d607b97c5fd0d22},
    /* 1e-44 */ {0xe45c10c42a2b3b05, 0x8cb89a7db77c506a}, {0x8eb98a7a9a5b04e3, 0x77f3608e92adb242},
    /* 1e-42 */ {0xb267ed1940f1c61c, 0x55f038b237591ed3}, {0xdf01e85f912e37a3, 0x6b6c46dec52f6688},
    /* 1e-40 */ {0x8b61313bbabce2c6, 0x2323ac4b3b3da015}, {0xae397d8aa96c1b77, 0xabec975e0a0d081a},
    /* 1e-38 */ {0xd9c7dced53c72255, 0x96e7bd358c904a21}, {0x881cea14545c7575, 0x7e50d64177da2e54},
    /* 1e-36 */ {0xaa242499697392d2, 0xdde50bd1d5d0b9e9}, {0xd4ad2dbfc3d07787, 0x955e4ec64b44e864},
    /* 1e-34 */ {0x84ec3c97da624ab4, 0xbd5af13bef0b113e}, {0xa6274bbdd0fadd61, 0xecb1ad8aeacdd58e},
    /* 1e-32 */ {0xcfb11ead453994ba, 0x67de18eda5814af2}, {0x81ceb32c4b43fcf4, 0x80eacf948770ced7},
    /* 1e-30 */ {0xa2425ff75e14fc31, 0xa1258379a94d028d}, {0xcad2f7f5359a3b3e, 0x096ee45813a04330},
    /* 1e-28 */ {0xfd87b5f28300ca0d, 0x8bca9d6e188853fc}, {0x9e74d1b791e07e48, 0x775ea264cf55347d},
    /* 1e-26 */ {0xc612062576589dda, 0x95364afe032a819d}, {0xf79687aed3eec551, 0x3a83ddbd83f52204},
    /* 1e-24 */ {0x9abe14cd44753b52, 0xc4926a9672793542}, {0xc16d9a0095928a27, 0x75b7053c0f178293},
    /* 1e-22 */ {0xf1c90080baf72cb1, 0x5324c68b12dd6338}, {0x971da05074da7bee, 0xd3f6fc16ebca5e03},
    /* 1e-20 */ {0xbce5086492111aea, 0x88f4bb1ca6bcf584}, {0xec1e4a7db69561a5, 0x2b31e9e3d06c32e5},
    /* 1e-18 */ {0x9392ee8e921d5d07, 0x3aff322e62439fcf}, {0xb877aa3236a4b449, 0x09befeb9fad487c2},
    /* 1e-16 */ {0xe69594bec44de15b, 0x4c2ebe687989a9b3}, {0x901d7cf73ab0acd9, 0x0f9d37014bf60a10},
    /* 1e-14 */ {0xb424dc35095cd80f, 0x538484c19ef38c94}, {0xe12e13424bb40e13, 0x2865a5f206b06fb9},
    /* 1e-12 */ {0x8cbccc096f5088cb, 0xf93f87b7442e45d3}, {0xafebff0bcb24aafe, 0xf78f69a51539d748},
    /* 1e-10 */ {0xdbe6fecebdedd5be, 0xb573440e5a884d1b}, {0x89705f4136b4a597, 0x31680a88f8953030},
    /* 1e-8 */ {0xabcc77118461cefc, 0xfdc20d2b36ba7c3d}, {0xd6bf94d5e57a42bc, 0x3d32907604691b4c},
    /* 1e-6 */ {0x8637bd05af6c69b5, 0xa63f9a49c2c1b10f}, {0xa7c5ac471b478423, 0x0fcf80dc33721d53},
    /* 1e-4 */ {0xd1b71758e219652b, 0xd3c36113404ea4a8}, {0x83126e978d4fdf3b, 0x645a1cac083126e9},
    /* 1e-2 */ {0xa3d70a3d70a3d70a, 0x3d70a3d70a3d70a3}, {0xcccccccccccccccc, 0xcccccccccccccccc},
    /* 1e0 */ {0x8000000000000000, 0x0000000000000000}, {0xa000000000000000, 0x0000000000000000},
    /* 1e2 */ {0xc800000000000000, 0x0000000000000000}, {0xfa00000000000000, 0x0000000000000000},
    /* 1e4 */ {0x9c40000000000000, 0x0000000000000000}, {0xc350000000000000, 0x0000000000000000},
    /* 1e6 */ {0xf424000000000000, 0x0000000000000000}, {0x9896800000000000, 0x0000000000000000},
    /* 1e8 */ {0xbebc200000000000, 0x0000000000000000}, {0xee6b280000000000, 0x0000000000000000},
    /* 1e10 */ {0x9502f90000000000, 0x0000000000000000}, {0xba43b74000000000, 0x0000000000000000},
    /* 1e12 */ {0xe8d4a51000000000, 0x0000000000000000}, {0x9184e72a00000000, 0x0000000000000000},
    /* 1e14 */ {0xb5e620f480000000, 0x0000000000000000}, {0xe35fa931a0000000, 0x0000000000000000},
    /* 1e16 */ {0x8e1bc9bf04000000, 0x0000000000000000}, {0xb1a2bc2ec5000000, 0x0000000000000000},
    /* 1e18 */ {0xde0b6b3a76400000, 0x0000000000000000}, {0x8ac7230489e80000, 0x0000000000000000},
    /* 1e20 */ {0xad78ebc5ac620000, 0x0000000000000000}, {0xd8d726b7177a8000, 0x0000000000000000},
    /* 1e22 */ {0x878678326eac9000, 0x0000000000000000}, {0xa968163f0a57b400, 0x0000000000000000},
    /* 1e24 */ {0xd3c21bcecceda100, 0x0000000000000000}, {0x84595161401484a0, 0x0000000000000000},
    /* 1e26 */ {0xa56fa5b99019a5c8, 0x0000000000000000}, {0xcecb8f27f4200f3a, 0x0000000000000000},
    /* 1e28 */ {0x813f3978f8940984, 0x4000000000000000}, {0xa18f07d736b90be5, 0x5000000000000000},
    /* 1e30 */ {0xc9f2c9cd04674ede, 0xa400000000000000}, {0xfc6f7c4045812296, 0x4d00000000000000},
    /* 1e32 */ {0x9dc5ada82b70b59d, 0xf020000000000000}, {0xc5371912364ce305, 0x6c28000000000000},
    /* 1e34 */ {0xf684df56c3e01bc6, 0xc732000000000000}, {0x9a130b963a6c115c, 0x3c7f400000000000},
    /* 1e36 */ {0xc097ce7bc90715b3, 0x4b9f100000000000}, {0xf0bdc21abb48db20, 0x1e86d40000000000},
    /* 1e38 */ {0x96769950b50d88f4, 0x1314448000000000}, {0xbc143fa4e250eb31, 0x17d955a000000000},
    /* 1e40 */ {0xeb194f8e1ae525fd, 0x5dcfab0800000000}, {0x92efd1b8d0cf37be, 0x5aa1cae500000000},
    /* 1e42 */ {0xb7abc627050305ad, 0xf14a3d9e40000000}, {0xe596b7b0c643c719, 0x6d9ccd05d0000000},
    /* 1e44 */ {0x8f7e32ce7bea5c6f, 0xe4820023a2000000}, {0xb35dbf821ae4f38b, 0xdda2802c8a800000},
    /* 1e46 */ {0xe0352f62a19e306e, 0xd50b2037ad200000}, {0x8c213d9da502de45, 0x4526f422cc340000},
    /* 1e48 */ {0xaf298d050e4395d6, 0x9670b12b7f410000}, {0xdaf3f04651d47b4c, 0x3c0cdd765f114000},
    /* 1e50 */ {0x88d8762bf324cd0f, 0xa5880a69fb6ac800}, {0xab0e93b6efee0053, 0x8eea0d047a457a00},
    /* 1e52 */ {0xd5d238a4abe98068, 0x72a4904598d6d880}, {0x85a36366eb71f041, 0x47a6da2b7f864750},
    /* 1e54 */ {0xa70c3c40a64e6c51, 0x999090b65f67d924}, {0xd0cf4b50cfe20765, 0xfff4b4e3f741cf6d},
    /* 1e56 */ {0x82818f1281ed449f, 0xbff8f10e7a8921a4}, {0xa321f2d7226895c7, 0xaff72d52192b6a0d},
    /* 1e58 */ {0xcbea6f8ceb02bb39, 0x9bf4f8a69f764490}, {0xfee50b7025c36a08, 0x02f236d04753d5b4},
    /* 1e60 */ {0x9f4f2726179a2245, 0x01d762422c946590}, {0xc722f0ef9d80aad6, 0x424d3ad2b7b97ef5},
    /* 1e62 */ {0xf8ebad2b84e0d58b, 0xd2e0898765a7deb2}, {0x9b934c3b330c8577, 0x63cc55f49f88eb2f},
    /* 1e64 */ {0xc2781f49ffcfa6d5, 0x3cbf6b71c76b25fb}, {0xf316271c7fc3908a, 0x8bef464e3945ef7a},
    /* 1e66 */ {0x97edd871cfda3a56, 0x97758bf0e3cbb5ac}, {0xbde94e8e43d0c8ec, 0x3d52eeed1cbea317},
    /* 1e68 */ {0xed63a231d4c4fb27, 0x4ca7aaa863ee4bdd}, {0x945e455f24fb1cf8, 0x8fe8caa93e74ef6a},
    /* 1e70 */ {0xb975d6b6ee39e436, 0xb3e2fd538e122b44}, {0xe7d34c64a9c85d44, 0x60dbbca87196b616},
    /* 1e72 */ {0x90e40fbeea1d3a4a, 0xbc8955e946fe31cd}, {0xb51d13aea4a488dd, 0x6babab6398bdbe41},
    /* 1e74 */ {0xe264589a4dcdab14, 0xc696963c7eed2dd1}, {0x8d7eb76070a08aec, 0xfc1e1de5cf543ca2},
    /* 1e76 */ {0xb0de65388cc8ada8, 0x3b25a55f43294bcb}, {0xdd15fe86affad912, 0x49ef0eb713f39ebe},
    /* 1e78 */ {0x8a2dbf142dfcc7ab, 0x6e3569326c784337}, {0xacb92ed9397bf996, 0x49c2c37f07965404},
    /* 1e80 */ {0xd7e77a8f87daf7fb, 0xdc33745ec97be906}, {0x86f0ac99b4e8dafd, 0x69a028bb3ded71a3},
    /* 1e82 */ {0xa8acd7c0222311bc, 0xc40832ea0d68ce0c}, {0xd2d80db02aabd62b, 0xf50a3fa490c30190},
    /* 1e84 */ {0x83c7088e1aab65db, 0x792667c6da79e0fa}, {0xa4b8cab1a1563f52, 0x577001b891185938},
    /* 1e86 */ {0xcde6fd5e09abcf26, 0xed4c0226b55e6f86}, {0x80b05e5ac60b6178, 0x544f8158315b05b4},
    /* 1e88 */ {0xa0dc75f1778e39d6, 0x696361ae3db1c721}, {0xc913936dd571c84c, 0x03bc3a19cd1e38e9},
    /* 1e90 */ {0xfb5878494ace3a5f, 0x04ab48a04065c723}, {0x9d174b2dcec0e47b, 0x62eb0d64283f9c76},
    /* 1e92 */ {0xc45d1df942711d9a, 0x3ba5d0bd324f8394}, {0xf5746577930d6500, 0xca8f44ec7ee36479},
    /* 1e94 */ {0x9968bf6abbe85f20, 0x7e998b13cf4e1ecb}, {0xbfc2ef456ae276e8, 0x9e3fedd8c321a67e},
    /* 1e96 */ {0xefb3ab16c59b14a2, 0xc5cfe94ef3ea101e}, {0x95d04aee3b80ece5, 0xbba1f1d158724a12},
    /* 1e98 */ {0xbb445da9ca61281f, 0x2a8a6e45ae8edc97}, {0xea1575143cf97226, 0xf52d09d71a3293bd},
    /* 1e100 */ {0x924d692ca61be758, 0x593c2626705f9c56}, {0xb6e0c377cfa2e12e, 0x6f8b2fb00c77836c},
    /* 1e102 */ {0xe498f455c38b997a, 0x0b6dfb9c0f956447}, {0x8edf98b59a373fec, 0x4724bd4189bd5eac},
    /* 1e104 */ {0xb2977ee300c50fe7, 0x58edec91ec2cb657}, {0xdf3d5e9bc0f653e1, 0x2f2967b66737e3ed},
    /* 1e106 */ {0x8b865b215899f46c, 0xbd79e0d20082ee74}, {0xae67f1e9aec07187, 0xecd8590680a3aa11},
    /* 1e108 */ {0xda01ee641a708de9, 0xe80e6f4820cc9495}, {0x884134fe908658b2, 0x3109058d147fdcdd},
    /* 1e110 */ {0xaa51823e34a7eede, 0xbd4b46f0599fd415}, {0xd4e5e2cdc1d1ea96, 0x6c9e18ac7007c91a},
    /* 1e112 */ {0x850fadc09923329e, 0x03e2cf6bc604ddb0}, {0xa6539930bf6bff45, 0x84db8346b786151c},
    /* 1e114 */ {0xcfe87f7cef46ff16, 0xe612641865679a63}, {0x81f14fae158c5f6e, 0x4fcb7e8f3f60c07e},
    /* 1e116 */ {0xa26da3999aef7749, 0xe3be5e330f38f09d}, {0xcb090c8001ab551c, 0x5cadf5bfd3072cc5},
    /* 1e118 */ {0xfdcb4fa002162a63, 0x73d9732fc7c8f7f6}, {0x9e9f11c4014dda7e, 0x2867e7fddcdd9afa},
    /* 1e120 */ {0xc646d63501a1511d, 0xb281e1fd541501b8}, {0xf7d88bc24209a565, 0x1f225a7ca91a4226},
    /* 1e122 */ {0x9ae757596946075f, 0x3375788de9b06958}, {0xc1a12d2fc3978937, 0x0052d6b1641c83ae},
    /* 1e124 */ {0xf209787bb47d6b84, 0xc0678c5dbd23a49a}, {0x9745eb4d50ce6332, 0xf840b7ba963646e0},
    /* 1e126 */ {0xbd176620a501fbff, 0xb650e5a93bc3d898}, {0xec5d3fa8ce427aff, 0xa3e51f138ab4cebe},
    /* 1e128 */ {0x93ba47c980e98cdf, 0xc66f336c36b10137}, {0xb8a8d9bbe123f017, 0xb80b0047445d4184},
    /* 1e130 */ {0xe6d3102ad96cec1d, 0xa60dc059157491e5}, {0x9043ea1ac7e41392, 0x87c89837ad68db2f},
    /* 1e132 */ {0xb454e4a179dd1877, 0x29babe4598c311fb}, {0xe16a1dc9d8545e94, 0xf4296dd6fef3d67a},
    /* 1e134 */ {0x8ce2529e2734bb1d, 0x1899e4a65f58660c}, {0xb01ae745b101e9e4, 0x5ec05dcff72e7f8f},
    /* 1e136 */ {0xdc21a1171d42645d, 0x76707543f4fa1f73}, {0x899504ae72497eba, 0x6a06494a791c53a8},
    /* 1e138 */ {0xabfa45da0edbde69, 0x0487db9d17636892}, {0xd6f8d7509292d603, 0x45a9d2845d3c42b6},
    /* 1e140 */ {0x865b86925b9bc5c2, 0x0b8a2392ba45a9b2}, {0xa7f26836f282b732, 0x8e6cac7768d7141e},
    /* 1e142 */ {0xd1ef0244af2364ff, 0x3207d795430cd926}, {0x8335616aed761f1f, 0x7f44e6bd49e807b8},
    /* 1e144 */ {0xa402b9c5a8d3a6e7, 0x5f16206c9c6209a6}, {0xcd036837130890a1, 0x36dba887c37a8c0f},
    /* 1e146 */ {0x802221226be55a64, 0xc2494954da2c9789}, {0xa02aa96b06deb0fd, 0xf2db9baa10b7bd6c},
    /* 1e148 */ {0xc83553c5c8965d3d, 0x6f92829494e5acc7}, {0xfa42a8b73abbf48c, 0xcb772339ba1f17f9},
    /* 1e150 */ {0x9c69a97284b578d7, 0xff2a760414536efb}, {0xc38413cf25e2d70d, 0xfef5138519684aba},
    /* 1e152 */ {0xf46518c2ef5b8cd1, 0x7eb258665fc25d69}, {0x98bf2f79d5993802, 0xef2f773ffbd97a61},
    /* 1e154 */ {0xbeeefb584aff8603, 0xaafb550ffacfd8fa}, {0xeeaaba2e5dbf6784, 0x95ba2a53f983cf38},
    /* 1e156 */ {0x952ab45cfa97a0b2, 0xdd945a747bf26183}, {0xba756174393d88df, 0x94f971119aeef9e4},
    /* 1e158 */ {0xe912b9d1478ceb17, 0x7a37cd5601aab85d}, {0x91abb422ccb812ee, 0xac62e055c10ab33a},
    /* 1e160 */ {0xb616a12b7fe617aa, 0x577b986b314d6009}, {0xe39c49765fdf9d94, 0xed5a7e85fda0b80b},
    /* 1e162 */ {0x8e41ade9fbebc27d, 0x14588f13be847307}, {0xb1d219647ae6b31c, 0x596eb2d8ae258fc8},
    /* 1e164 */ {0xde469fbd99a05fe3, 0x6fca5f8ed9aef3bb}, {0x8aec23d680043bee, 0x25de7bb9480d5854},
    /* 1e166 */ {0xada72ccc20054ae9, 0xaf561aa79a10ae6a}, {0xd910f7ff28069da4, 0x1b2ba1518094da04},
    /* 1e168 */ {0x87aa9aff79042286, 0x90fb44d2f05d0842}, {0xa99541bf57452b28, 0x353a1607ac744a53},
    /* 1e170 */ {0xd3fa922f2d1675f2, 0x42889b8997915ce8}, {0x847c9b5d7c2e09b7, 0x69956135febada11},
    /* 1e172 */ {0xa59bc234db398c25, 0x43fab9837e699095}, {0xcf02b2c21207ef2e, 0x94f967e45e03f4bb},
    /* 1e174 */ {0x8161afb94b44f57d, 0x1d1be0eebac278f5}, {0xa1ba1ba79e1632dc, 0x6462d92a69731732},
    /* 1e176 */ {0xca28a291859bbf93, 0x7d7b8f7503cfdcfe}, {0xfcb2cb35e702af78, 0x5cda735244c3d43e},
    /* 1e178 */ {0x9defbf01b061adab, 0x3a0888136afa64a7}, {0xc56baec21c7a1916, 0x088aaa1845b8fdd0},
    /* 1e180 */ {0xf6c69a72a3989f5b, 0x8aad549e57273d45}, {0x9a3c2087a63f6399, 0x36ac54e2f678864b},
    /* 1e182 */ {0xc0cb28a98fcf3c7f, 0x84576a1bb416a7dd}, {0xf0fdf2d3f3c30b9f, 0x656d44a2a11c51d5},
    /* 1e184 */ {0x969eb7c47859e743, 0x9f644ae5a4b1b325}, {0xbc4665b596706114, 0x873d5d9f0dde1fee},
    /* 1e186 */ {0xeb57ff22fc0c7959, 0xa90cb506d155a7ea}, {0x9316ff75dd87cbd8, 0x09a7f12442d588f2},
    /* 1e188 */ {0xb7dcbf5354e9bece, 0x0c11ed6d538aeb2f}, {0xe5d3ef282a242e81, 0x8f1668c8a86da5fa},
    /* 1e190 */ {0x8fa475791a569d10, 0xf96e017d694487bc}, {0xb38d92d760ec4455, 0x37c981dcc395a9ac},
    /* 1e192 */ {0xe070f78d3927556a, 0x85bbe253f47b1417}, {0x8c469ab843b89562, 0x93956d7478ccec8e},
    /* 1e194 */ {0xaf58416654a6babb, 0x387ac8d1970027b2}, {0xdb2e51bfe9d0696a, 0x06997b05fcc0319e},
    /* 1e196 */ {0x88fcf317f22241e2, 0x441fece3bdf81f03}, {0xab3c2fddeeaad25a, 0xd527e81cad7626c3},
    /* 1e198 */ {0xd60b3bd56a5586f1, 0x8a71e223d8d3b074}, {0x85c7056562757456, 0xf6872d5667844e49},
    /* 1e200 */ {0xa738c6bebb12d16c, 0xb428f8ac016561db}, {0xd106f86e69d785c7, 0xe13336d701beba52},
    /* 1e202 */ {0x82a45b450226b39c, 0xecc0024661173473}, {0xa34d721642b06084, 0x27f002d7f95d0190},
    /* 1e204 */ {0xcc20ce9bd35c78a5, 0x31ec038df7b441f4}, {0xff290242c83396ce, 0x7e67047175a15271},
    /* 1e206 */ {0x9f79a169bd203e41, 0x0f0062c6e984d386}, {0xc75809c42c684dd1, 0x52c07b78a3e60868},
    /* 1e208 */ {0xf92e0c3537826145, 0xa7709a56ccdf8a82}, {0x9bbcc7a142b17ccb, 0x88a66076400bb691},
    /* 1e210 */ {0xc2abf989935ddbfe, 0x6acff893d00ea435}, {0xf356f7ebf83552fe, 0x0583f6b8c4124d43},
    /* 1e212 */ {0x98165af37b2153de, 0xc3727a337a8b704a}, {0xbe1bf1b059e9a8d6, 0x744f18c0592e4c5c},
    /* 1e214 */ {0xeda2ee1c7064130c, 0x1162def06f79df73}, {0x9485d4d1c63e8be7, 0x8addcb5645ac2ba8},
    /* 1e216 */ {0xb9a74a0637ce2ee1, 0x6d953e2bd7173692}, {0xe8111c87c5c1ba99, 0xc8fa8db6ccdd0437},
    /* 1e218 */ {0x910ab1d4db9914a0, 0x1d9c9892400a22a2}, {0xb54d5e4a127f59c8, 0x2503beb6d00cab4b},
    /* 1e220 */ {0xe2a0b5dc971f303a, 0x2e44ae64840fd61d}, {0x8da471a9de737e24, 0x5ceaecfed289e5d2},
    /* 1e222 */ {0xb10d8e1456105dad, 0x7425a83e872c5f47}, {0xdd50f1996b947518, 0xd12f124e28f77719},
    /* 1e224 */ {0x8a5296ffe33cc92f, 0x82bd6b70d99aaa6f}, {0xace73cbfdc0bfb7b, 0x636cc64d1001550b},
    /* 1e226 */ {0xd8210befd30efa5a, 0x3c47f7e05401aa4e}, {0x8714a775e3e95c78, 0x65acfaec34810a71},
    /* 1e228 */ {0xa8d9d1535ce3b396, 0x7f1839a741a14d0d}, {0xd31045a8341ca07c, 0x1ede48111209a050},
    /* 1e230 */ {0x83ea2b892091e44d, 0x934aed0aab460432}, {0xa4e4b66b68b65d60, 0xf81da84d5617853f},
    /* 1e232 */ {0xce1de40642e3f4b9, 0x36251260ab9d668e}, {0x80d2ae83e9ce78f3, 0xc1d72b7c6b426019},
    /* 1e234 */ {0xa1075a24e4421730, 0xb24cf65b8612f81f}, {0xc94930ae1d529cfc, 0xdee033f26797b627},
    /* 1e236 */ {0xfb9b7cd9a4a7443c, 0x169840ef017da3b1}, {0x9d412e0806e88aa5, 0x8e1f289560ee864e},
    /* 1e238 */ {0xc491798a08a2ad4e, 0xf1a6f2bab92a27e2}, {0xf5b5d7ec8acb58a2, 0xae10af696774b1db},
    /* 1e240 */ {0x9991a6f3d6bf1765, 0xacca6da1e0a8ef29}, {0xbff610b0cc6edd3f, 0x17fd090a58d32af3},
    /* 1e242 */ {0xeff394dcff8a948e, 0xddfc4b4cef07f5b0}, {0x95f83d0a1fb69cd9, 0x4abdaf101564f98e},
    /* 1e244 */ {0xbb764c4ca7a4440f, 0x9d6d1ad41abe37f1}, {0xea53df5fd18d5513, 0x84c86189216dc5ed},
    /* 1e246 */ {0x92746b9be2f8552c, 0x32fd3cf5b4e49bb4}, {0xb7118682dbb66a77, 0x3fbc8c33221dc2a1},
    /* 1e248 */ {0xe4d5e82392a40515, 0x0fabaf3feaa5334a}, {0x8f05b1163ba6832d, 0x29cb4d87f2a7400e},
    /* 1e250 */ {0xb2c71d5bca9023f8, 0x743e20e9ef511012}, {0xdf78e4b2bd342cf6, 0x914da9246b255416},
    /* 1e252 */ {0x8bab8eefb6409c1a, 0x1ad089b6c2f7548e}, {0xae9672aba3d0c320, 0xa184ac2473b529b1},
    /* 1e254 */ {0xda3c0f568cc4f3e8, 0xc9e5d72d90a2741e}, {0x8865899617fb1871, 0x7e2fa67c7a658892},
    /* 1e256 */ {0xaa7eebfb9df9de8d, 0xddbb901b98feeab7}, {0xd51ea6fa85785631, 0x552a74227f3ea565},
    /* 1e258 */ {0x8533285c936b35de, 0xd53a88958f87275f}, {0xa67ff273b8460356, 0x8a892abaf368f137},
    /* 1e260 */ {0xd01fef10a657842c, 0x2d2b7569b0432d85}, {0x8213f56a67f6b29b, 0x9c3b29620e29fc73},
    /* 1e262 */ {0xa298f2c501f45f42, 0x8349f3ba91b47b8f}, {0xcb3f2f7642717713, 0x241c70a936219a73},
    /* 1e264 */ {0xfe0efb53d30dd4d7, 0xed238cd383aa0110}, {0x9ec95d1463e8a506, 0xf4363804324a40aa},
    /* 1e266 */ {0xc67bb4597ce2ce48, 0xb143c6053edcd0d5}, {0xf81aa16fdc1b81da, 0xdd94b7868e94050a},
    /* 1e268 */ {0x9b10a4e5e9913128, 0xca7cf2b4191c8326}, {0xc1d4ce1f63f57d72, 0xfd1c2f611f63a3f0},
    /* 1e270 */ {0xf24a01a73cf2dccf, 0xbc633b39673c8cec}, {0x976e41088617ca01, 0xd5be0503e085d813},
    /* 1e272 */ {0xbd49d14aa79dbc82, 0x4b2d8644d8a74e18}, {0xec9c459d51852ba2, 0xddf8e7d60ed1219e},
    /* 1e274 */ {0x93e1ab8252f33b45, 0xcabb90e5c942b503}, {0xb8da1662e7b00a17, 0x3d6a751f3b936243},
    /* 1e276 */ {0xe7109bfba19c0c9d, 0x0cc512670a783ad4}, {0x906a617d450187e2, 0x27fb2b80668b24c5},
    /* 1e278 */ {0xb484f9dc9641e9da, 0xb1f9f660802dedf6}, {0xe1a63853bbd26451, 0x5e7873f8a0396973},
    /* 1e280 */ {0x8d07e33455637eb2, 0xdb0b487b6423e1e8}, {0xb049dc016abc5e5f, 0x91ce1a9a3d2cda62},
    /* 1e282 */ {0xdc5c5301c56b75f7, 0x7641a140cc7810fb}, {0x89b9b3e11b6329ba, 0xa9e904c87fcb0a9d},
    /* 1e284 */ {0xac2820d9623bf429, 0x546345fa9fbdcd44}, {0xd732290fbacaf133, 0xa97c177947ad4095},
    /* 1e286 */ {0x867f59a9d4bed6c0, 0x49ed8eabcccc485d}, {0xa81f301449ee8c70, 0x5c68f256bfff5a74},
    /* 1e288 */ {0xd226fc195c6a2f8c, 0x73832eec6fff3111}, {0x83585d8fd9c25db7, 0xc831fd53c5ff7eab},
    /* 1e290 */ {0xa42e74f3d032f525, 0xba3e7ca8b77f5e55}, {0xcd3a1230c43fb26f, 0x28ce1bd2e55f35eb},
    /* 1e292 */ {0x80444b5e7aa7cf85, 0x7980d163cf5b81b3}, {0xa0555e361951c366, 0xd7e105bcc332621f},
    /* 1e294 */ {0xc86ab5c39fa63440, 0x8dd9472bf3fefaa7}, {0xfa856334878fc150, 0xb14f98f6f0feb951},
    /* 1e296 */ {0x9c935e00d4b9d8d2, 0x6ed1bf9a569f33d3}, {0xc3b8358109e84f07, 0x0a862f80ec4700c8},
    /* 1e298 */ {0xf4a642e14c6262c8, 0xcd27bb612758c0fa}, {0x98e7e9cccfbd7dbd, 0x8038d51cb897789c},
    /* 1e300 */ {0xbf21e44003acdd2c, 0xe0470a63e6bd56c3}, {0xeeea5d5004981478, 0x1858ccfce06cac74},
    /* 1e302 */ {0x95527a5202df0ccb, 0x0f37801e0c43ebc8}, {0xbaa718e68396cffd, 0xd30560258f54e6ba},
    /* 1e304 */ {0xe950df20247c83fd, 0x47c6b82ef32a2069}, {0x91d28b7416cdd27e, 0x4cdc331d57fa5441},
    /* 1e306 */ {0xb6472e511c81471d, 0xe0133fe4adf8e952}, {0xe3d8f9e563a198e5, 0x58180fddd97723a6},
    /* 1e308 */ {0x8e679c2f5e44ff8f, 0x570f09eaa7ea7648}, {0xb201833b35d63f73, 0x2cd2cc6551e513da},
    /* 1e310 */ {0xde81e40a034bcf4f, 0xf8077f7ea65e58d1}, {0x8b112e86420f6191, 0xfb04afaf27faf782},
    /* 1e312 */ {0xadd57a27d29339f6, 0x79c5db9af1f9b563}, {0xd94ad8b1c7380874, 0x18375281ae7822bc},
    /* 1e314 */ {0x87cec76f1c830548, 0x8f2293910d0b15b5}, {0xa9c2794ae3a3c69a, 0xb2eb3875504ddb22},
    /* 1e316 */ {0xd433179d9c8cb841, 0x5fa60692a46151eb}, {0x849feec281d7f328, 0xdbc7c41ba6bcd333},
    /* 1e318 */ {0xa5c7ea73224deff3, 0x12b9b522906c0800}, {0xcf39e50feae16bef, 0xd768226b34870a00},
    /* 1e320 */ {0x81842f29f2cce375, 0xe6a1158300d46640}, {0xa1e53af46f801c53, 0x60495ae3c1097fd0},
    /* 1e322 */ {0xca5e89b18b602368, 0x385bb19cb14bdfc4}, {0xfcf62c1dee382c42, 0x46729e03dd9ed7b5},
    /* 1e324 */ {0x9e19db92b4e31ba9, 0x6c07a2c26a8346d1},
};

/* zmij `Pow10SignificandsTable::get_unchecked`, dec_exp in -292..324. */
static inline elk_zmij_u128 elk_zmij_pow10_get(int32_t dec_exp) {
    const uint64_t *entry = elk_zmij_pow10[dec_exp + 292];
    elk_zmij_u128 r = {entry[0], entry[1]};
    return r;
}

/* zmij `compute_dec_exp`: floor(log10(2^bin_exp)) if regular, otherwise
 * floor(log10(3/4 * 2^bin_exp)). */
static inline int32_t elk_zmij_compute_dec_exp(int32_t bin_exp, int regular) {
    /* log10_2_sig = round(log10(2) * 2^20), log10_3_over_4_sig = -log10(3/4) * 2^20 rounded
     * to a power of two */
    return elk_zmij_asr(bin_exp * 315653 - (regular ? 0 : 131072), 20);
}

/* zmij `do_compute_exp_shift` (also the contents of zmij's `EXP_SHIFTS` table): a shift so that,
 * after scaling by 10^-dec_exp, the intermediate result has a fixed 128-bit fractional part. */
static inline unsigned elk_zmij_compute_exp_shift(int32_t bin_exp, int32_t dec_exp) {
    /* pow10_bin_exp = floor(log2(10^-dec_exp)), log2_pow10_sig = round(log2(10) * 2^16) + 1 */
    int32_t pow10_bin_exp = elk_zmij_asr(-dec_exp * 217707, 16);
    return (uint8_t)(bin_exp + pow10_bin_exp + 1);
}

/* zmij `ToDecimalResult`: sig * 10^exp. */
typedef struct {
    int64_t sig;
    int32_t exp;
} elk_zmij_dec;

/* zmij `to_decimal_schubfach` (u64): the Schubfach algorithm with strict overestimates of the
 * powers of 10, which guarantees correctness in the boundary cases of the fast path. */
static elk_zmij_dec elk_zmij_to_decimal_schubfach(uint64_t bin_sig, int32_t bin_exp, int regular) {
    const unsigned bound_shift = 2; /* shift the significand so that boundaries are integer */
    int32_t dec_exp = elk_zmij_compute_dec_exp(bin_exp, regular);
    unsigned exp_shift = elk_zmij_compute_exp_shift(bin_exp, dec_exp);
    elk_zmij_u128 pow10 = elk_zmij_pow10_get(-dec_exp);
    pow10.lo += 1; /* no entry has lo == 2^64 - 1 */

    uint64_t bin_sig_shifted = bin_sig << bound_shift;
    /* Estimates of the lower and upper bounds of the rounding interval, multiplied by the power
     * of 10 with modified rounding. */
    uint64_t lsb = bin_sig & 1;
    uint64_t lower = (bin_sig_shifted - ((uint64_t)(regular != 0) + 1)) << exp_shift;
    lower = elk_zmij_umulhi_inexact_to_odd(pow10.hi, pow10.lo, lower) + lsb;
    uint64_t upper = (bin_sig_shifted + 2) << exp_shift;
    upper = elk_zmij_umulhi_inexact_to_odd(pow10.hi, pow10.lo, upper) - lsb;

    /* A single shorter candidate (Cassio Neri), <= the upper bound by construction. */
    uint64_t shorter = (upper >> bound_shift) / 10 * 10;
    if ((shorter << bound_shift) >= lower) {
        elk_zmij_dec r = {(int64_t)shorter, dec_exp};
        return r;
    }

    uint64_t scaled_sig =
        elk_zmij_umulhi_inexact_to_odd(pow10.hi, pow10.lo, bin_sig_shifted << exp_shift);
    uint64_t longer_below = scaled_sig >> bound_shift;
    uint64_t longer_above = longer_below + 1;

    /* Pick the closest of longer_below and longer_above and check if it is in the rounding
     * interval (zmij: `cmp` as i64; < 0 iff bit 63 is set). */
    uint64_t cmp = scaled_sig - ((longer_below + longer_above) << 1);
    int below_closer = (cmp >> 63) != 0 || (cmp == 0 && (longer_below & 1) == 0);
    int below_in = (longer_below << bound_shift) >= lower;
    elk_zmij_dec r = {(int64_t)((below_closer && below_in) ? longer_below : longer_above), dec_exp};
    return r;
}

/* zmij `to_decimal_fast` (f64): converts bin_sig * 2^(raw_exp - 1075) to the shortest decimal,
 * with the yy_double fast path for regular values (falls back to Schubfach for exact half-ulp
 * ties, boundary cases and irregular values, i.e. powers of two). */
static inline elk_zmij_dec elk_zmij_to_decimal_fast(uint64_t bin_sig, int32_t raw_exp, int regular) {
    int32_t bin_exp = raw_exp - 1075;
    if (regular) {
        int32_t dec_exp = elk_zmij_compute_dec_exp(bin_exp, 1);
        unsigned exp_shift = elk_zmij_compute_exp_shift(bin_exp, dec_exp);
        elk_zmij_u128 pow10 = elk_zmij_pow10_get(-dec_exp);

        /* integral and fractional parts of bin_sig * pow10 */
        elk_zmij_u128 p = elk_zmij_umul192_hi128(pow10.hi, pow10.lo, bin_sig << exp_shift);
        uint64_t integral = p.hi;
        uint64_t fractional = p.lo;

        /* Exact half-ulp tie when rounding to the nearest integer (zmij: `cmp` as i64). */
        uint64_t cmp = fractional - ((uint64_t)1 << 63);
        if (cmp != 0) {
            /* integral % 10 by Dougall Johnson: (1 << 63) / 5 == (1 << 64) / 10. */
            const uint64_t div10_sig64 = ((uint64_t)1 << 63) / 5 + 1;
            uint64_t div10 = elk_zmij_umul128_hi64(integral, div10_sig64);
            uint64_t digit = integral - div10 * 10;

            /* Fixed point: the least significant integral digit in the upper 4 bits, fractional
             * digits in the lower 60 bits. */
            const unsigned num_integral_bits = 4;
            const unsigned num_fractional_bits = 60;
            const uint64_t ten = (uint64_t)10 << num_fractional_bits;
            /* fixed-point remainder of the scaled significand modulo 10 */
            uint64_t scaled_sig_mod10 = (digit << num_fractional_bits) | (fractional >> num_integral_bits);
            /* 0.5 * pow10 in the fixed-point format (1 ulp is in [1, 10) after scaling) */
            uint64_t scaled_half_ulp = pow10.hi >> (num_integral_bits - exp_shift + 1);
            uint64_t upper = scaled_sig_mod10 + scaled_half_ulp;

            /* Boundary case when rounding down to the nearest 10 and near-boundary case when
             * rounding up to the nearest 10 (upper == ten || upper == ten - 1). */
            if (!(ten - upper <= 1 || scaled_sig_mod10 == scaled_half_ulp)) {
                int round_up = upper >= ten;
                int64_t shorter = (int64_t)(integral - digit);
                int64_t longer = (int64_t)(integral + (uint64_t)((cmp >> 63) == 0));
                int64_t dec_sig = scaled_sig_mod10 < scaled_half_ulp ? shorter : longer;
                elk_zmij_dec r = {round_up ? shorter + 10 : dec_sig, dec_exp};
                return r;
            }
        }
    }
    return elk_zmij_to_decimal_schubfach(bin_sig, bin_exp, regular);
}

/* zmij `to_bcd8` (Xiang JunBo): the eight decimal digits of abcdefgh < 10^8, one per byte, the
 * most significant digit in the most significant byte (zmij then applies `to_be`). */
static inline uint64_t elk_zmij_to_bcd8(uint64_t abcdefgh) {
    const uint64_t div10k_sig = ((uint64_t)1 << 40) / 10000 + 1;
    const uint64_t neg10k = ((uint64_t)1 << 32) - 10000;
    const uint64_t div100_sig = ((uint64_t)1 << 19) / 100 + 1;
    const uint64_t neg100 = ((uint64_t)1 << 16) - 100;
    const uint64_t div10_sig = ((uint64_t)1 << 10) / 10 + 1;
    const uint64_t neg10 = ((uint64_t)1 << 8) - 10;
    uint64_t abcd_efgh = abcdefgh + neg10k * ((abcdefgh * div10k_sig) >> 40);
    uint64_t ab_cd_ef_gh =
        abcd_efgh + neg100 * (((abcd_efgh * div100_sig) >> 19) & UINT64_C(0x7f0000007f));
    return ab_cd_ef_gh + neg10 * (((ab_cd_ef_gh * div10_sig) >> 10) & UINT64_C(0xf000f000f000f));
}

/* Writes the eight ASCII digits of a `to_bcd8` group (zmij `write8(buffer, bcd + ZEROS)`). */
static inline void elk_zmij_write8(char *buffer, uint64_t bcd) {
    const uint64_t zeros = UINT64_C(0x0101010101010101) * (uint64_t)'0';
#if (defined(__GNUC__) || defined(__clang__)) && defined(__BYTE_ORDER__) && \
    __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    uint64_t v = __builtin_bswap64(bcd) + zeros;
    memcpy(buffer, &v, sizeof v);
#elif (defined(__GNUC__) || defined(__clang__)) && defined(__BYTE_ORDER__) && \
    __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
    uint64_t v = bcd + zeros;
    memcpy(buffer, &v, sizeof v);
#else
    (void)zeros;
    for (int i = 0; i < 8; i++) {
        buffer[i] = (char)('0' + ((bcd >> (56 - 8 * i)) & 0xff));
    }
#endif
}

/* Digits of a `to_bcd8` group up to its last nonzero digit (zmij `count_trailing_nonzeros`). */
static inline unsigned elk_zmij_bcd_len(uint64_t bcd) {
#if defined(__GNUC__) || defined(__clang__)
    return bcd == 0 ? 0 : 8 - ((unsigned)__builtin_ctzll(bcd) >> 3);
#else
    unsigned n = 8;
    while (n > 0 && (bcd & 0xff) == 0) {
        bcd >>= 8;
        n--;
    }
    return n;
#endif
}

/* zmij `write_significand` (f64, portable path): writes the significand (16-17 digits for
 * normals) without trailing zeros and returns the end. */
static inline char *elk_zmij_write_significand(char *buffer, uint64_t value, int extra_digit) {
    /* value = abbccddeeffgghhii */
    uint32_t abbccddee = (uint32_t)(value / 100000000);
    uint32_t ffgghhii = (uint32_t)(value % 100000000);
    buffer[0] = (char)('0' + abbccddee / 100000000);
    buffer += extra_digit != 0;
    uint64_t bcd = elk_zmij_to_bcd8(abbccddee % 100000000);
    elk_zmij_write8(buffer, bcd);
    if (ffgghhii == 0) {
        return buffer + elk_zmij_bcd_len(bcd);
    }
    bcd = elk_zmij_to_bcd8(ffgghhii);
    elk_zmij_write8(buffer + 8, bcd);
    return buffer + 8 + elk_zmij_bcd_len(bcd);
}

#define ELK_ZMIJ_THRESHOLD INT64_C(10000000000000000) /* 10^16 */

/* Second half of zmij `write::<f64>`: lays out dec.sig * 10^dec.exp (dec.sig has 16 or 17
 * digits; trailing zeros allowed) at `buffer` (the position after the sign) and returns the end.
 * Positional for decimal exponents -5..15 (`12.0`, `0.001234`, `1234567890123456.0`), otherwise
 * `d.ddde+XX` / `d.ddde-XX`; with `plus_exp == 0` nonnegative exponents are written without the
 * sign (ryu `1e21`). */
static char *elk_zmij_write_dec(char *buffer, elk_zmij_dec dec, int plus_exp) {
    int extra_digit = dec.sig >= ELK_ZMIJ_THRESHOLD;
    int32_t dec_exp = dec.exp + 15 + extra_digit; /* exponent of the leading digit */

    char *end = elk_zmij_write_significand(buffer + 1, (uint64_t)dec.sig, extra_digit);
    int32_t length = (int32_t)(end - (buffer + 1));

    if (dec_exp >= -5 && dec_exp <= 15) {
        if (length - 1 <= dec_exp) {
            /* 1234e7 -> 12340000000.0 */
            memmove(buffer, buffer + 1, (size_t)length);
            memset(buffer + length, '0', (size_t)(dec_exp + 3 - length));
            buffer[dec_exp + 1] = '.';
            return buffer + dec_exp + 3;
        } else if (0 <= dec_exp) {
            /* 1234e-2 -> 12.34 */
            memmove(buffer, buffer + 1, (size_t)(dec_exp + 1));
            buffer[dec_exp + 1] = '.';
            return buffer + length + 1;
        } else {
            /* 1234e-6 -> 0.001234 */
            memmove(buffer + (1 - dec_exp), buffer + 1, (size_t)length);
            memset(buffer, '0', (size_t)(1 - dec_exp));
            buffer[1] = '.';
            return buffer + (1 - dec_exp) + length;
        }
    }

    /* 1234e30 -> 1.234e33 */
    buffer[0] = buffer[1];
    buffer[1] = '.';
    buffer += length + (length > 1);
    *buffer++ = 'e';
    if (dec_exp < 0) {
        *buffer++ = '-';
        dec_exp = -dec_exp;
    } else if (plus_exp) {
        *buffer++ = '+';
    }
    if (dec_exp >= 100) {
        *buffer++ = (char)('0' + dec_exp / 100);
        dec_exp %= 100;
        *buffer++ = (char)('0' + dec_exp / 10);
    } else if (dec_exp >= 10) {
        *buffer++ = (char)('0' + dec_exp / 10);
    }
    *buffer++ = (char)('0' + dec_exp % 10);
    return buffer;
}

/* zmij `write::<f64>` (`Buffer::format_finite`): writes the shortest correctly rounded decimal
 * representation of the finite double `value` to `buffer` (>= 25 bytes) and returns the end.
 * `plus_exp` as in `elk_zmij_write_dec`. */
static char *elk_zmij_write(double value, char *buffer, int plus_exp) {
    uint64_t bits;
    memcpy(&bits, &value, sizeof bits);
    int32_t bin_exp = (int32_t)((bits << 1) >> 53); /* raw binary exponent */
    uint64_t bin_sig = bits & (((uint64_t)1 << 52) - 1);

    *buffer = '-';
    buffer += bits >> 63;

    elk_zmij_dec dec;
    if (bin_exp == 0) {
        if (bin_sig == 0) {
            buffer[0] = '0';
            buffer[1] = '.';
            buffer[2] = '0';
            return buffer + 3;
        }
        dec = elk_zmij_to_decimal_schubfach(bin_sig, 1 - 1075, 1);
        while (dec.sig < ELK_ZMIJ_THRESHOLD) {
            dec.sig *= 10;
            dec.exp -= 1;
        }
    } else {
        dec = elk_zmij_to_decimal_fast(bin_sig | ((uint64_t)1 << 52), bin_exp, bin_sig != 0);
    }
    return elk_zmij_write_dec(buffer, dec, plus_exp);
}

/* Digits of `elk_float_to_shortest` for a normal power of two (irregular rounding interval).
 * Earlier elk-lean versions took the first precision p = 1..17 whose correctly rounded `%.*e`
 * output round-trips; for powers of two that can be one digit longer than the shortest
 * representation in the asymmetric rounding interval that zmij finds (`2^-777`:
 * `6.290184345309701e-235` vs `6.2901843453097005e-235`; 46 of the 2046 normal powers of two
 * differ). `Float.toShortest` keeps the old digits for all normal powers of two (cheap for the
 * common short ones such as 0.5 or 1024); everything else uses zmij, which gives the same output
 * as the old search there (verified on 26.7M doubles). */
static elk_zmij_dec elk_shortest_dec_pow2(double x) {
    char buf[48];
    for (int p = 1; p <= 17; p++) { /* 17 significant digits always round-trip */
        snprintf(buf, sizeof buf, "%.*e", p - 1, x);
        if (strtod(buf, NULL) == x) {
            break;
        }
    }
    /* buf = [-]d[.ddd]e(+|-)XX */
    const char *s = buf + (buf[0] == '-');
    int64_t sig = 0;
    int nd = 0;
    for (; *s && *s != 'e'; s++) {
        if (*s != '.') {
            sig = sig * 10 + (*s - '0');
            nd++;
        }
    }
    int e10 = atoi(s + 1);
    for (; nd < 17; nd++) {
        sig *= 10;
    }
    elk_zmij_dec dec = {sig, e10 - 16};
    return dec;
}

/* ---- Lean entry points ------------------------------------------------------------------- */

static lean_obj_res elk_float_nonfinite_name(double x) {
    if (isnan(x)) {
        return lean_mk_string("NaN");
    }
    return lean_mk_string(x > 0 ? "inf" : "-inf");
}

/* `elk_float_to_shortest` into `buffer` (>= 32 bytes) for a finite x; returns the end. */
static char *elk_shortest_write(double x, char *buffer) {
    uint64_t bits;
    memcpy(&bits, &x, sizeof bits);
    if ((bits & (((uint64_t)1 << 52) - 1)) == 0 && ((bits << 1) >> 53) != 0) {
        *buffer = '-';
        return elk_zmij_write_dec(buffer + (bits >> 63), elk_shortest_dec_pow2(x), 0);
    }
    return elk_zmij_write(x, buffer, 0);
}

/* Shortest round-trip representation, ryu style: `12.0`, `0.1`, `1234.5`, `1e21`, `1.5e-7`,
 * `-0.0`, `NaN`, `inf`, `-inf` (zmij digits, see `elk_shortest_dec_pow2` for powers of two). */
LEAN_EXPORT lean_obj_res elk_float_to_shortest(double x) {
    if (!isfinite(x)) {
        return elk_float_nonfinite_name(x);
    }
    char buf[32];
    size_t n = (size_t)(elk_shortest_write(x, buf) - buf);
    return lean_mk_string_unchecked(buf, n, n);
}

/* JSON number of a finite double exactly as the elk-rs oracle prints it: serde_json 1.0.149
 * (zmij 1.0.19 `format_finite`) shortest round-trip digits, positional for decimal exponents
 * -5..15 (`12.0`, `0.001234`, `1234567890123456.0`), otherwise `d.ddde+XX` / `d.ddde-XX`.
 * Non-finite values (never passed by the JSON printer) give `NaN` / `inf` / `-inf`. */
LEAN_EXPORT lean_obj_res elk_float_to_json(double x) {
    if (!isfinite(x)) {
        return elk_float_nonfinite_name(x);
    }
    char buf[32];
    size_t n = (size_t)(elk_zmij_write(x, buf, 1) - buf);
    return lean_mk_string_unchecked(buf, n, n);
}

/* ---- Output buffers of the JSON printer ------------------------------------------------------
 * The printer threads one string through all appends. These helpers append several pieces (or a
 * formatted number) in one call: the capacity is ensured once, and no temporary string is made. */

/* `s` (consumed) unshared with room for `extra` more bytes: `s` itself when it is exclusive and has
 * the capacity, otherwise a copy with the capacity grown geometrically (like `lean_string_append`). */
static lean_obj_res elk_string_reserve(lean_obj_arg s, size_t extra) {
    size_t sz = lean_string_size(s); /* bytes including the terminator */
    size_t cap = lean_string_capacity(s);
    if (lean_is_exclusive(s) && cap >= sz + extra) {
        return s;
    }
    size_t ncap = cap + sz + extra;
    lean_object *r = lean_alloc_string(sz, ncap, lean_string_len(s));
    memcpy(lean_to_string(r)->m_data, lean_string_cstr(s), sz);
    lean_dec_ref(s);
    return r;
}

/* Appends `n` bytes (`len` characters) to a string reserved by `elk_string_reserve`. */
static inline void elk_string_put(lean_object *s, const char *p, size_t n, size_t len) {
    lean_string_object *o = lean_to_string(s);
    memcpy(o->m_data + o->m_size - 1, p, n);
    o->m_size += n;
    o->m_length += len;
    o->m_data[o->m_size - 1] = 0;
}

/* Appends the Lean string `a`. */
static inline void elk_string_put_str(lean_object *s, b_lean_obj_arg a) {
    elk_string_put(s, lean_string_cstr(a), lean_string_size(a) - 1, lean_string_len(a));
}

/* `elk_float_to_json` of a finite x, `null` otherwise, into `buf` (>= 32 bytes); returns the length. */
static size_t elk_json_float_write(double x, char *buf) {
    if (!isfinite(x)) {
        memcpy(buf, "null", 4);
        return 4;
    }
    return (size_t)(elk_zmij_write(x, buf, 1) - buf);
}

/* `(Number.ofFloatElk x).render` into `buf` (>= 32 bytes); returns the length: a finite, exactly
 * integral x other than `-0.0` with |x| < 2^63 as a decimal integer, any other finite x as
 * `elk_float_to_json`, a non-finite one as `null`. */
static size_t elk_elk_number_write(double x, char *buf) {
    if (!isfinite(x)) {
        memcpy(buf, "null", 4);
        return 4;
    }
    uint64_t bits;
    memcpy(&bits, &x, sizeof bits);
    if (x == round(x) && bits != 0x8000000000000000ULL && fabs(x) < 9223372036854775808.0) {
        int64_t v = (int64_t)x;
        uint64_t u = v < 0 ? (uint64_t)0 - (uint64_t)v : (uint64_t)v;
        char tmp[24];
        size_t k = 0;
        do {
            tmp[k++] = (char)('0' + (int)(u % 10));
            u /= 10;
        } while (u != 0);
        size_t n = 0;
        if (v < 0) {
            buf[n++] = '-';
        }
        while (k > 0) {
            buf[n++] = tmp[--k];
        }
        return n;
    }
    return (size_t)(elk_zmij_write(x, buf, 1) - buf);
}

/* An empty string with room for `cap` bytes (output buffers of the JSON printer). */
LEAN_EXPORT lean_obj_res elk_string_with_capacity(size_t cap) {
    lean_object *r = lean_alloc_string(1, cap + 1, 0);
    lean_to_string(r)->m_data[0] = 0;
    return r;
}

/* `s ++ Number.render (.float x)`: `elk_float_to_json` for a finite x, `null` otherwise. */
LEAN_EXPORT lean_obj_res elk_string_append_json_float(lean_obj_arg s, double x) {
    char buf[32];
    size_t n = elk_json_float_write(x, buf);
    s = elk_string_reserve(s, n);
    elk_string_put(s, buf, n, n);
    return s;
}

/* `s ++ (Number.ofFloatElk x).render`. */
LEAN_EXPORT lean_obj_res elk_string_append_elk_number(lean_obj_arg s, double x) {
    char buf[32];
    size_t n = elk_elk_number_write(x, buf);
    s = elk_string_reserve(s, n);
    elk_string_put(s, buf, n, n);
    return s;
}

/* `s ++ pre ++ (Number.ofFloatElk x).render`. */
LEAN_EXPORT lean_obj_res elk_string_append_pre_elk_number(lean_obj_arg s, b_lean_obj_arg pre, double x) {
    char buf[32];
    size_t n = elk_elk_number_write(x, buf);
    s = elk_string_reserve(s, lean_string_size(pre) - 1 + n);
    elk_string_put_str(s, pre);
    elk_string_put(s, buf, n, n);
    return s;
}

/* `s ++ pre ++ "{\"x\":" ++ X ++ ",\"y\":" ++ Y ++ "}"` with the layout numbers X, Y of x, y
 * (`Number.ofFloatElk`): a point object of the transfer. */
LEAN_EXPORT lean_obj_res elk_string_append_point(lean_obj_arg s, b_lean_obj_arg pre, double x, double y) {
    char buf[96];
    size_t n = 0;
    memcpy(buf, "{\"x\":", 5);
    n = 5;
    n += elk_elk_number_write(x, buf + n);
    memcpy(buf + n, ",\"y\":", 5);
    n += 5;
    n += elk_elk_number_write(y, buf + n);
    buf[n++] = '}';
    s = elk_string_reserve(s, lean_string_size(pre) - 1 + n);
    elk_string_put_str(s, pre);
    elk_string_put(s, buf, n, n);
    return s;
}

/* `s ++ a ++ b ++ c`. */
LEAN_EXPORT lean_obj_res elk_string_append3(lean_obj_arg s, b_lean_obj_arg a, b_lean_obj_arg b, b_lean_obj_arg c) {
    s = elk_string_reserve(s, lean_string_size(a) + lean_string_size(b) + lean_string_size(c) - 3);
    elk_string_put_str(s, a);
    elk_string_put_str(s, b);
    elk_string_put_str(s, c);
    return s;
}

/* Java `Double.toString` style is not needed for JSON, but `%.17g` is handy for traces. */
LEAN_EXPORT lean_obj_res elk_float_to_g17(double x) {
    char out[64];
    snprintf(out, sizeof out, "%.17g", x);
    return lean_mk_string(out);
}

/* Correctly rounded parse. The caller validates the lexeme; this returns NaN
 * when nothing could be parsed. */
LEAN_EXPORT double elk_strtod(b_lean_obj_arg s) {
    const char *str = lean_string_cstr(s);
    char *end = NULL;
    double v = strtod(str, &end);
    if (end == str) {
        return NAN;
    }
    return v;
}

/* Seconds since the Unix epoch (`perf_benchmark` CSV timestamps). Lean >= 4.2x compiles
 * `BaseIO` externs without a world token and returns the value directly. */
LEAN_EXPORT lean_obj_res elk_unix_time(void) {
    time_t t = time(NULL);
    return lean_usize_to_nat((size_t)(t < 0 ? 0 : t));
}

/* Fast paths of `Float.ofScientific` / `Float.ofNat` / `Float.ofInt` (see Elk/Core/Util/FastFloat.lean).
 * Exactly the core fast path: a mantissa below 2^53 is exact as a double and 10^e (e <= 22) is
 * exactly representable, so one IEEE division / multiplication gives the same correctly rounded
 * result as the Lean implementation. NaN means "not handled" (the Lean wrapper falls back). */
static const double elk_pow10_exact[23] = {
    1e0, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9, 1e10, 1e11,
    1e12, 1e13, 1e14, 1e15, 1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22};

LEAN_EXPORT double elk_float_of_sci_fast(b_lean_obj_arg m, uint8_t s, b_lean_obj_arg e) {
    if (lean_is_scalar(m) && lean_is_scalar(e)) {
        uint64_t mv = (uint64_t)lean_unbox(m);
        uint64_t ev = (uint64_t)lean_unbox(e);
        if (mv < ((uint64_t)1 << 53) && ev <= 22) {
            double dm = (double)(uint64_t)mv;
            return s ? dm / elk_pow10_exact[ev] : dm * elk_pow10_exact[ev];
        }
    }
    return NAN;
}

LEAN_EXPORT double elk_float_of_nat_fast(b_lean_obj_arg n) {
    if (lean_is_scalar(n)) {
        uint64_t v = (uint64_t)lean_unbox(n);
        if (v < ((uint64_t)1 << 53)) {
            return (double)(uint64_t)v;
        }
    }
    return NAN;
}

LEAN_EXPORT double elk_float_of_int_fast(b_lean_obj_arg i) {
    if (lean_is_scalar(i)) {
        int64_t v = lean_scalar_to_int64(i);
        if (v > -((int64_t)1 << 53) && v < ((int64_t)1 << 53)) {
            return (double)v;
        }
    }
    return NAN;
}
