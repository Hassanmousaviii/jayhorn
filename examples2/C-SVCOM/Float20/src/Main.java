import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {
    
    static final int FULP = 1;

    static void bug(float min) {
        // 0x1.fffffep-105f ≈ 7.4505806e-32f
        if (!(min == 0x1.fffffep-105f)) {
            return;
        }

        float modifier = (float) (0x1.0p-23) * (1 << FULP);  // 2^-23 = 1.1920929e-7f
        float ulpdiff = min * modifier;

        // 0x1p-126f ≈ 1.1754944e-38f
        if (!(ulpdiff == 0x1p-126f)) {
           assert false;
        }
    }

    static void bugBrokenOut(float min) {
        // 0x1.fffffep-105f ≈ 7.4505806e-32f
        if (!(min == 0x1.fffffep-105f)) {
            return;
        }

            float modifier = (float) ((0x1.0p-23) * (1 << FULP));
            double dulpdiff = (double) min * (double) modifier;
            float ulpdiff = (float) dulpdiff;

            // 0x1p-126f ≈ 1.1754944e-38f
            if (!(ulpdiff == 0x1p-126f)) {
                assert false;
            }
    }


    static void bugCasting(double d) {
        // 0x1.fffffep-127 ≈ 1.1754942e-38
        if (!(d == 0x1.fffffep-127)) {
            return;
        }

        float f = (float) d;

        // 0x1p-126f ≈ 1.1754944e-38f
        if (!(f == 0x1p-126f)) {
           assert false;
        }
    }

    public static void main(String[] args) {
        float f = Verifier.nondetFloat();
        bug(f);

      /*  float g = Verifier.nondetFloat();
        bugBrokenOut(g);

        double d = Verifier.nondetFloat();
        bugCasting(d);*/
    }
}