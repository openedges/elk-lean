// Differential harness for elk-lean's `Elk.Core.Util.javaAsin` (JDK `FdLibm.Asin`, = HotSpot `Math.asin`).
// Prints "argumentBits resultBits" (hex) of `Math.asin` for the branch boundaries and <n> random
// arguments of every branch (seed 42):
//
//   javac -d <dir> scripts/java/AsinDump.java && java -cp <dir> AsinDump 400000 > <file>
//   ELK_ASIN_CASES=<file> lake test -- --suite spv.javaAsin
import java.util.Random;
/** Prints "inputBits resultBits" of Math.asin for edge cases and n random arguments in [-1, 1]. */
public final class AsinDump {
    public static void main(String[] a) {
        int n = Integer.parseInt(a[0]);
        double[] edge = {1.0, -1.0, 0.0, -0.0, 0.5, -0.5, 0.49999999999999994, 0.975, -0.975, 0.9749999999999999,
            0.97500000000001, 1e-10, -1e-10, 1e-300, 3.725290298461914E-9, 7.450580596923828E-9, 0.3, -0.7, 0.99999999,
            -0.99999999, 1.0000000000000002, -1.5, 2.0, Double.NaN, Double.POSITIVE_INFINITY, Double.MIN_VALUE};
        StringBuilder sb = new StringBuilder();
        for (double x : edge) sb.append(Long.toHexString(Double.doubleToRawLongBits(x))).append(' ')
            .append(Long.toHexString(Double.doubleToRawLongBits(Math.asin(x)))).append('\n');
        Random r = new Random(42);
        for (int i = 0; i < n; i++) {
            double x;
            switch (i % 4) {
                case 0: x = r.nextDouble() * 2 - 1; break;
                case 1: x = (r.nextDouble() * 2 - 1) * 0.5; break;
                case 2: x = 0.97 + r.nextDouble() * 0.03; break;
                default: x = Math.scalb(r.nextDouble(), -r.nextInt(40)) * (r.nextBoolean() ? 1 : -1);
            }
            sb.append(Long.toHexString(Double.doubleToRawLongBits(x))).append(' ')
              .append(Long.toHexString(Double.doubleToRawLongBits(Math.asin(x)))).append('\n');
        }
        System.out.print(sb);
    }
}
