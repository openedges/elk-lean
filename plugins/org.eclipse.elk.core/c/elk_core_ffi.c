/*
 * elk-lean C helpers for org.eclipse.elk.core.
 *
 * Lean's `Float.toString` prints with a fixed number of decimals, which is
 * neither round-trip safe nor compatible with the reference JSON output of
 * elkjs / elk-rs. `elk_float_to_shortest` produces the shortest decimal
 * representation that round-trips, formatted like serde_json (ryu "pretty"):
 *   12.0   0.1   1234.5   1e21   1.5e-7   -0.0
 * `elk_strtod` is a correctly rounded decimal-to-double conversion.
 */
#include <lean/lean.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int shortest_digits(double x, char *buf, size_t n) {
    for (int prec = 1; prec <= 17; prec++) {
        snprintf(buf, n, "%.*e", prec - 1, x);
        if (strtod(buf, NULL) == x) {
            return prec;
        }
    }
    snprintf(buf, n, "%.16e", x);
    return 17;
}

/* `plus_exp`: write positive exponents with a sign (`1e+21`), as serde_json >= 1.0.149
 * (zmij) does; otherwise ryu style (`1e21`). */
static lean_obj_res format_shortest(double x, int plus_exp) {
    char out[64];
    if (isnan(x)) {
        return lean_mk_string("NaN");
    }
    if (isinf(x)) {
        return lean_mk_string(x > 0 ? "inf" : "-inf");
    }
    if (x == 0.0) {
        return lean_mk_string(signbit(x) ? "-0.0" : "0.0");
    }
    char buf[48];
    shortest_digits(x, buf, sizeof buf);
    const char *p = buf;
    int neg = 0;
    if (*p == '-') {
        neg = 1;
        p++;
    }
    char digits[32];
    int nd = 0;
    for (; *p && *p != 'e'; p++) {
        if (*p != '.') {
            digits[nd++] = *p;
        }
    }
    digits[nd] = 0;
    int e10 = atoi(p + 1);
    while (nd > 1 && digits[nd - 1] == '0') {
        digits[--nd] = 0;
    }
    /* value = 0.d1d2...dn * 10^kk */
    int kk = e10 + 1;
    char *o = out;
    if (neg) {
        *o++ = '-';
    }
    if (kk > 0 && kk <= 16 && nd <= kk) {
        memcpy(o, digits, (size_t)nd);
        o += nd;
        for (int i = nd; i < kk; i++) {
            *o++ = '0';
        }
        *o++ = '.';
        *o++ = '0';
        *o = 0;
    } else if (kk > 0 && kk <= 16) {
        memcpy(o, digits, (size_t)kk);
        o += kk;
        *o++ = '.';
        memcpy(o, digits + kk, (size_t)(nd - kk));
        o += nd - kk;
        *o = 0;
    } else if (kk > -5 && kk <= 0) {
        *o++ = '0';
        *o++ = '.';
        for (int i = 0; i < -kk; i++) {
            *o++ = '0';
        }
        memcpy(o, digits, (size_t)nd);
        o += nd;
        *o = 0;
    } else {
        *o++ = digits[0];
        if (nd > 1) {
            *o++ = '.';
            memcpy(o, digits + 1, (size_t)(nd - 1));
            o += nd - 1;
        }
        if (plus_exp && kk - 1 >= 0) {
            sprintf(o, "e+%d", kk - 1);
        } else {
            sprintf(o, "e%d", kk - 1);
        }
    }
    return lean_mk_string(out);
}

LEAN_EXPORT lean_obj_res elk_float_to_shortest(double x) {
    return format_shortest(x, 0);
}

/* JSON number of a finite double exactly as the elk-rs oracle prints it: serde_json 1.0.149
 * (zmij 1.0.19) shortest round-trip digits, positional for decimal exponents -5..15
 * (`12.0`, `0.001234`, `1234567890123456.0`), otherwise `d.ddde+XX` / `d.ddde-XX`. */
LEAN_EXPORT lean_obj_res elk_float_to_json(double x) {
    return format_shortest(x, 1);
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
