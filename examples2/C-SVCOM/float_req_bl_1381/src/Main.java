import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

   
    static float copysignFloat(float x, float y) {
        int ix = Float.floatToIntBits(x);
        int iy = Float.floatToIntBits(y);
        int resultBits = (ix & 0x7fffffff) | (iy & 0x80000000);
        return Float.intBitsToFloat(resultBits);
    }

    static boolean isnanFloat(float x) {
        return x != x;
    }

    public static void main(String[] args) {
        /*
         * REQ-BL-1381:
         * The copysign and copysignf procedures shall return NaN if the argument x is NaN.
         */

        float x = 0.0f / 0.0f; // NaN
        float y = Verifier.nondetFloat();
        float res = copysignFloat(x, y);

        // x is NaN, y can be any, the result shall be NaN
        if (!isnanFloat(res)) {
           assert false;
        }
    }
}