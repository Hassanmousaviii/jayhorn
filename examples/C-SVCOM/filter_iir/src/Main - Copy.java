import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    // Coefficients from the C code
    static final double A1_0 = 1.0;
    static final double A1_1 = 0.5179422053046;
    static final double A1_2 = 1.0;
    static final double b1_0 = 1.470767736573;
    static final double b1_1 = 0.5522073405779;

    static final double A2_0 = 1.0;
    static final double A2_1 = 1.633101801841;
    static final double A2_2 = 1.0;
    static final double b2_0 = 1.742319554830;
    static final double b2_1 = 0.820939679242;

    // State variables (replacing arrays)
    static double D1_0 = 0.0;
    static double D1_1 = 0.0;
    static double D2_0 = 0.0;
    static double D2_1 = 0.0;

    static double X = 0.0;
    static double P = 0.0;

   
    public static void main(String[] args) {
        while (P >= -1e30 && P <= 1e30) {
            X = Verifier.nondetDouble();
            Verifier.assume(X >= -10.0 && X <= 10.0);

            iir4();
        }
        assert false;
    }

    // Main filtering logic
    static void iir4() {
        double x1 = 0.0117749388721091 * X;

        double t1 = x1 + b1_0 * D1_0 - b1_1 * D1_1;
        double y1 = A1_0 * t1 - A1_1 * D1_0 + A1_2 * D1_1;

        D1_1 = D1_0;
        D1_0 = t1;

        double t2 = y1 + b2_0 * D2_0 - b2_1 * D2_1;
        P = A2_0 * t2 - A2_1 * D2_0 + A2_2 * D2_1;

        D2_1 = D2_0;
        D2_0 = t2;
    }

    
}