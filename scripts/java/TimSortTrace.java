// Differential harness for elk-lean's `Elk.Core.Util.JavaSort` (port of OpenJDK 21 java.util.TimSort).
//
//   javac -d <dir> scripts/java/TimSortTrace.java
//   java -cp <dir> TimSortTrace gen <out.jsonl> [full|fixture]
//   java -cp <dir> TimSortTrace dump <n> <keyKind> <mod> <neg> <cmpKind> <seed> <k>
//
// `gen` writes one JSON object per line and case: the case parameters, a hash of the generated keys
// (the Lean side regenerates the keys with the same generator and checks the hash), the outcome of
// `Collections.sort(new ArrayList<>(elements), comparator)` ("ok", "IAE" = IllegalArgumentException
// "Comparison method violates its general contract!", "throw" = the comparator's own exception,
// "other:<class>: <message>"), the number of comparator calls, the FNV-1a 64 hash of the comparator
// call sequence (ids a, b and sign + 1 of each call; 3 for the call that throws) and, for "ok", the
// FNV-1a 64 hash of the resulting permutation of ids (plus the permutation itself when n <= 64).
// `dump` prints the full call sequence and permutation of one case (for debugging a divergence).
//
// Generator (mirrored in tests/lean/Tests/Core/JavaSort.lean): mix = splitmix64 finaliser after
// adding the golden gamma, h3(seed, a, b) = mix(seed ^ mix(a * 1000003 ^ mix(b))), all on unsigned
// 64-bit values (Java long arithmetic wraps like UInt64; % is Long.remainderUnsigned).
import java.io.*;
import java.util.*;

public final class TimSortTrace {
  static long mix(long z) {
    z += 0x9E3779B97F4A7C15L;
    z = (z ^ (z >>> 30)) * 0xBF58476D1CE4E5B9L;
    z = (z ^ (z >>> 27)) * 0x94D049BB133111EBL;
    return z ^ (z >>> 31);
  }

  static long h3(long seed, long a, long b) { return mix(seed ^ mix((a * 1000003L) ^ mix(b))); }

  static long umod(long x, long m) { return Long.remainderUnsigned(x, m); }

  static final long FNV_OFFSET = 0xcbf29ce484222325L;
  static final long FNV_PRIME = 0x100000001b3L;

  static long fnv(long h, long x) { return (h ^ x) * FNV_PRIME; }

  /** Element: original index and key (key < 0 = "undefined", e.g. a port without side). */
  static final class E {
    final int id;
    final long key;
    E(int id, long key) { this.id = id; this.key = key; }
  }

  /** Keys of a case (see the key kinds in tests/lean/Tests/Core/JavaSort.lean). */
  static long[] keys(int n, int keyKind, long mod, long neg, long seed) {
    long[] k = new long[n];
    int i = 0;
    int seg = 0;
    while (i < n) {
      switch (keyKind) {
        case 0: k[i] = umod(h3(seed, i, 1), mod); i++; break;
        case 1: k[i] = ((long) i * mod) / n; i++; break;
        case 2: k[i] = ((long) (n - 1 - i) * mod) / n; i++; break;
        case 3: {
          long r = h3(seed, seg, 3);
          seg++;
          long len = 1 + umod(r >>> 8, 64) * (umod(r, 4) == 0 ? 8 : 1);
          long dir = umod(r >>> 20, 3);
          long v0 = umod(r >>> 32, mod);
          for (long j = 0; j < len && i < n; j++, i++) {
            k[i] = dir == 0 ? v0 + j : dir == 1 ? v0 + len - j : v0;
          }
          break;
        }
        case 4: k[i] = 0; i++; break;
        case 5: k[i] = umod(i, mod); i++; break;
        default: {
          long r = h3(seed, i, 6);
          k[i] = umod(r, 16) == 0 ? umod(r >>> 8, n) : i;
          i++;
        }
      }
    }
    if (neg > 0) {
      for (int j = 0; j < n; j++) if (umod(h3(seed, j, 99), neg) == 0) k[j] = -1;
    }
    return k;
  }

  static int ord3(long r) {
    long x = umod(r, 3);
    return x == 0 ? -1 : x == 1 ? 0 : 1;
  }

  /** The comparator's own exception (kinds 11 and 12). */
  static final class CmpThrow extends RuntimeException {
    CmpThrow(String m) { super(m); }
  }

  /** Comparator kinds (see tests/lean/Tests/Core/JavaSort.lean `cmpRaw`); results are -1/0/1. */
  static int cmpRaw(int kind, long seed, long kth, long calls, E x, E y) {
    long a = x.id, b = y.id;
    switch (kind) {
      case 0: return Long.compare(x.key, y.key);
      case 1: { int c = Long.compare(x.key, y.key); return c != 0 ? c : Integer.compare(x.id, y.id); }
      case 2: return Long.compare(y.key, x.key);
      case 3: return 0;
      case 4: return ord3(h3(seed, a, b));
      case 5: {
        if (a == b) return 0;
        return umod(h3(seed, Math.min(a, b), Math.max(a, b)), 2) == 0 ? -1 : 1;
      }
      case 6: return -1;
      case 7: return 1;
      case 8: {
        if (a == b) return 0;
        long lo = Math.min(a, b), hi = Math.max(a, b);
        int o = umod(h3(seed, lo, hi), 2) == 0 ? -1 : 1;
        return a < b ? o : -o;
      }
      case 9: {
        long r = h3(seed, a, b);
        return umod(r, 16) == 0 ? ord3(r >>> 8) : Long.compare(x.key, y.key);
      }
      case 10: return (x.key < 0 || y.key < 0) ? 0 : Long.compare(x.key, y.key);
      case 11:
        if (calls == kth) throw new CmpThrow("call " + kth);
        return Long.compare(x.key, y.key);
      default:
        if (x.key < 0 || y.key < 0) throw new CmpThrow("Port side is undefined");
        return Long.compare(x.key, y.key);
    }
  }

  static final class Result {
    String outcome;
    long calls;
    long cmpHash = FNV_OFFSET;
    int[] perm;
    List<long[]> seq;
  }

  static Result run(int n, int keyKind, long mod, long neg, int cmpKind, long seed, long kth, boolean keepSeq) {
    long[] k = keys(n, keyKind, mod, neg, seed);
    List<E> list = new ArrayList<>();
    for (int i = 0; i < n; i++) list.add(new E(i, k[i]));
    Result res = new Result();
    if (keepSeq) res.seq = new ArrayList<>();
    Comparator<E> c = (x, y) -> {
      res.calls++;
      int r;
      try {
        r = cmpRaw(cmpKind, seed, kth, res.calls, x, y);
      } catch (CmpThrow t) {
        res.cmpHash = fnv(fnv(fnv(res.cmpHash, x.id), y.id), 3);
        if (keepSeq) res.seq.add(new long[] {x.id, y.id, 2});
        throw t;
      }
      res.cmpHash = fnv(fnv(fnv(res.cmpHash, x.id), y.id), r + 1);
      if (keepSeq) res.seq.add(new long[] {x.id, y.id, r});
      return r;
    };
    try {
      Collections.sort(list, c);
      res.outcome = "ok";
      res.perm = new int[n];
      for (int i = 0; i < n; i++) res.perm[i] = list.get(i).id;
    } catch (CmpThrow t) {
      res.outcome = "throw";
    } catch (IllegalArgumentException e) {
      res.outcome = "Comparison method violates its general contract!".equals(e.getMessage())
          ? "IAE" : "other:" + e.getClass().getName() + ": " + e.getMessage();
    } catch (RuntimeException e) {
      res.outcome = "other:" + e.getClass().getName() + ": " + e.getMessage();
    }
    return res;
  }

  static long keysHash(long[] k) {
    long h = FNV_OFFSET;
    for (long x : k) h = fnv(h, x);
    return h;
  }

  static long permHash(int[] p) {
    long h = FNV_OFFSET;
    for (int x : p) h = fnv(h, x);
    return h;
  }

  static final int CMP_KINDS = 13;
  static final int KEY_KINDS = 7;

  /** One case: derives mod/neg/k from the case seed. */
  static void emit(PrintWriter out, int n, int keyKind, int cmpKind, long seed) {
    long r = h3(seed, n, 0xC0FFEE);
    long[] mods = {2, 3, 5, 10, n / 4 + 1, n + 1, 1000000007L};
    long mod = mods[(int) umod(r, mods.length)];
    long neg = 0;
    if (cmpKind == 10 || cmpKind == 12) neg = 1 + umod(r >>> 16, 40);
    else if (umod(r >>> 16, 8) == 0) neg = 1 + umod(r >>> 24, 10);
    int bits = 64 - Long.numberOfLeadingZeros(n);
    long kth = 1 + umod(r >>> 32, (long) n * bits + 1);
    Result res = run(n, keyKind, mod, neg, cmpKind, seed, kth, false);
    StringBuilder sb = new StringBuilder();
    sb.append("{\"n\":").append(n).append(",\"keyKind\":").append(keyKind).append(",\"mod\":").append(mod)
        .append(",\"neg\":").append(neg).append(",\"cmp\":").append(cmpKind)
        .append(",\"seed\":\"").append(Long.toUnsignedString(seed)).append('"')
        .append(",\"k\":").append(kth)
        .append(",\"keysHash\":\"").append(Long.toUnsignedString(keysHash(keys(n, keyKind, mod, neg, seed)))).append('"')
        .append(",\"outcome\":\"").append(res.outcome.replace("\"", "'")).append('"')
        .append(",\"calls\":").append(res.calls)
        .append(",\"cmpHash\":\"").append(Long.toUnsignedString(res.cmpHash)).append('"');
    if (res.perm != null) {
      sb.append(",\"permHash\":\"").append(Long.toUnsignedString(permHash(res.perm))).append('"');
      if (n <= 64) {
        sb.append(",\"perm\":[");
        for (int i = 0; i < n; i++) sb.append(i == 0 ? "" : ",").append(res.perm[i]);
        sb.append(']');
      }
    }
    sb.append('}');
    out.println(sb);
  }

  public static void main(String[] args) throws IOException {
    if (args.length >= 8 && args[0].equals("dump")) {
      Result res = run(Integer.parseInt(args[1]), Integer.parseInt(args[2]), Long.parseLong(args[3]),
          Long.parseLong(args[4]), Integer.parseInt(args[5]), Long.parseUnsignedLong(args[6]),
          Long.parseLong(args[7]), true);
      System.out.println("outcome " + res.outcome + " calls " + res.calls);
      for (long[] s : res.seq) System.out.println(s[0] + " " + s[1] + " " + s[2]);
      if (res.perm != null) System.out.println("perm " + Arrays.toString(res.perm));
      return;
    }
    if (args.length < 2 || !args[0].equals("gen")) {
      System.err.println("usage: TimSortTrace gen <out.jsonl> [full|fixture] | dump n keyKind mod neg cmp seed k");
      System.exit(2);
    }
    boolean fixture = args.length > 2 && args[2].equals("fixture");
    long count = 0;
    try (PrintWriter out = new PrintWriter(new BufferedWriter(new FileWriter(args[1])))) {
      List<Integer> sizes = new ArrayList<>();
      int[] seeds;
      if (fixture) {
        for (int n = 0; n <= 40; n++) sizes.add(n);
        for (int n : new int[] {63, 64, 65, 100, 129, 257, 600}) sizes.add(n);
      } else {
        for (int n = 0; n <= 70; n++) sizes.add(n);
        for (int n : new int[] {95, 96, 97, 127, 128, 129, 191, 192, 255, 256, 257, 383, 511, 512, 513,
                                1023, 1024, 1025, 2047, 2048, 2049})
          sizes.add(n);
      }
      int si = 0;
      for (int n : sizes) {
        int reps = fixture ? 1 : (n <= 70 ? 1 : 2);
        for (int rep = 0; rep < reps; rep++) {
          for (int cmp = 0; cmp < CMP_KINDS; cmp++) {
            for (int kk = 0; kk < KEY_KINDS; kk++) {
              long seed = h3(0x5EED0000L + si, cmp * 16 + kk, rep);
              // fixture: a deterministic ~1/10 sample of the small sizes, all kinds of the larger ones
              if (fixture && n <= 40 && umod(seed, 10) != 0) continue;
              if (fixture && n > 40 && kk % 3 != 0) continue;
              emit(out, n, kk, cmp, seed);
              count++;
            }
          }
        }
        si++;
      }
      if (!fixture) {
        // random sizes between the thresholds, and large arrays
        for (int j = 0; j < 60; j++) {
          int n = 71 + (int) umod(h3(0xABCDEF, j, 0), 1930);
          for (int cmp = 0; cmp < CMP_KINDS; cmp++)
            for (int kk = 0; kk < KEY_KINDS; kk += 2) {
              emit(out, n, kk, cmp, h3(0x5EED1000L + j, cmp * 16 + kk, 0));
              count++;
            }
        }
        for (int n : new int[] {3000, 4000, 4999, 5000}) {
          for (int cmp = 0; cmp < CMP_KINDS; cmp++)
            for (int kk = 0; kk < KEY_KINDS; kk++) {
              emit(out, n, kk, cmp, h3(0x5EED2000L + n, cmp * 16 + kk, 0));
              count++;
            }
        }
      }
    }
    System.err.println("cases: " + count);
  }
}
