// Differential harness for elk-lean's `Elk.Core.Util.javaSin`/`javaCos` (the HotSpot aarch64 `Math.sin`/
// `Math.cos` stubs, including the large-argument reduction `__kernel_rem_pio2` above 2^19·π/2).
// Prints "argumentBits sinBits cosBits" (hex) of `Math.sin`/`Math.cos` for boundary arguments and <n>
// random arguments spread over all magnitudes up to the largest finite double (seed 42):
//
//   javac -d <dir> scripts/java/SinCosDump.java && java -cp <dir> SinCosDump 1000000 > <file>
//   ELK_SINCOS_CASES=<file> lake test -- --suite core.javaSinCos.large
import java.util.Random;
/** Prints "inputBits sinBits cosBits" of Math.sin/Math.cos for edge cases and n random arguments. */
public final class SinCosDump {
    private static final StringBuilder SB = new StringBuilder();

    private static void emit(double x) {
        SB.append(Long.toHexString(Double.doubleToRawLongBits(x))).append(' ')
          .append(Long.toHexString(Double.doubleToRawLongBits(Math.sin(x)))).append(' ')
          .append(Long.toHexString(Double.doubleToRawLongBits(Math.cos(x)))).append('\n');
    }

    public static void main(String[] a) {
        int n = Integer.parseInt(a[0]);
        // the medium/large boundary (high word 0x413921fb) and its neighbours, powers of two, multiples of π/2
        long[] bits = {0x413921fb00000000L, 0x413921fbffffffffL, 0x413921fc00000000L, 0x413921fa54442d18L,
            0x413921fb54442d18L, 0x413921fb54442d19L, 0x7fefffffffffffffL, 0x7fe0000000000000L, 0x4170000000000000L};
        for (long b : bits) { emit(Double.longBitsToDouble(b)); emit(-Double.longBitsToDouble(b)); }
        for (int e = 19; e <= 1023; e++) {
            double p = Math.scalb(1.0, e);
            emit(p); emit(-p); emit(Math.nextUp(p)); emit(Math.nextDown(p));
            emit(p * (Math.PI / 2)); emit(Math.nextUp(p * (Math.PI / 2)));
        }
        double[] edge = {1e22, 1e300, -1e300, 1.7976931348623157e308, 6381956970095103.0 * Math.scalb(1.0, 797),
            5.319372648326541e255, 1e15, 1e16, 1e17, 3.14159265358979e10, 823550.0, 823549.6, 1e6, 1e7, 1e8};
        for (double x : edge) emit(x);
        Random r = new Random(42);
        for (int i = 0; i < n; i++) {
            double x;
            switch (i % 4) {
                // uniform in the exponent from 2^19 to the largest finite double
                case 0: x = Math.scalb(1.0 + r.nextDouble(), 19 + r.nextInt(1005)); break;
                // random bits with a large exponent
                case 1: x = Double.longBitsToDouble((r.nextLong() & 0x000fffffffffffffL)
                        | ((long) (0x413 + r.nextInt(0x7ff - 0x413)) << 52)); break;
                // near multiples of π/2 above the medium range
                case 2: x = Math.rint(Math.scalb(r.nextDouble(), 20 + r.nextInt(40))) * (Math.PI / 2); break;
                // decimal magnitudes up to 1e300
                default: x = (1.0 + 9.0 * r.nextDouble()) * Math.pow(10, 6 + r.nextInt(295));
            }
            if (Double.isInfinite(x) || Double.isNaN(x)) x = 1e300;
            emit(r.nextBoolean() ? x : -x);
        }
        System.out.print(SB);
    }
}
