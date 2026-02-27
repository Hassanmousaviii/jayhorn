import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    

    // Quake fast inverse square root
    static float invSqrt(float x) {
        float xhalf = 0.5f * x;
        int i = Float.floatToIntBits(x);
        //i = 0x5f3759df - (i >> 1);
        x = Float.intBitsToFloat(i);
        x = x * (1.5f - xhalf * x * x); // Newton's method
        return x;
    }

    public static void main(String[] args) {
        float a =  Verifier.nondetFloat();
        Verifier.assume(a >= 0.1f && a <= 100.0f);

        float r = invSqrt(a);
        assert(r >= 0.0f && r <= 10.0f);
    }
}