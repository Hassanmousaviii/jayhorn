import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
   
    static void wait_for_clock() {
        // No-op in this context
    }

    public static void main(String[] args) {
        int i;
        float x = 0.0f;

        for (i = 0; i < 3000000; i++) {
            if (Verifier.nondetInt() != 0) {
                x = Verifier.nondetFloat();
                Verifier.assume(x >= -100.0f && x <= 100.0f);
            }

            x = x / 3.1f;
            x = x * 3.1f;

            wait_for_clock();
        }

        assert(x >= -1000.0f && x <= 1000.0f);
    }
}