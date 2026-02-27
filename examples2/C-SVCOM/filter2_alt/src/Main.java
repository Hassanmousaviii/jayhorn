import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    static boolean INIT;
    static float P, X;

    static float E0 = 0.0f, E1 = 0.0f;
    static float S0 = 0.0f, S1 = 0.0f;

  
    static float RANDOM_INPUT() {
        float x = Verifier.nondetFloat();
        Verifier.assume(x >= -10.f && x <= 10.f);
        return x;
    }

    static void filter2() {
        if (INIT) {
            S0 = X;
            P = X;
            E0 = X;
        } else {
            P = (((((0.4677826f * X)
                    - (E0 * 0.7700725f))
                    + (E1 * 0.4344376f))
                    + (S0 * 1.5419f))
                    - (S1 * 0.6740477f));
            assert(P >= -15.f && P <= 15.f);
        }

        // Update state
        E1 = E0;
        E0 = X;
        S1 = S0;
        S0 = P;
    }

    public static void main(String[] args) {
        X = RANDOM_INPUT();
        INIT = true;

        while (true) {
            X = RANDOM_INPUT();
            filter2();
            INIT = false;
        }
    }
}