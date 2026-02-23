import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    public static double inv(double A) {
        long A_bits = Double.doubleToRawLongBits(A);
        int exp = (int) ((A_bits & 0x7FF0000000000000L) >>> 52) - 1023;
        long xi_bits = ((long)(1023 - exp)) << 52;
        double xi = Double.longBitsToDouble(xi_bits);
        boolean cond = true;

        while (cond) {
            double xsi = 2 * xi - A * xi * xi;
            double temp = xsi - xi;
            cond = (temp > 1e-10) || (temp < -1e-10);
            xi = xsi;
        }
        return xi;
    }

    public static void main(String[] args){
        double a = Verifier.nondetDouble();
        Verifier.assume(a >= 20.0 && a <= 30.0);
        double r = inv(a);
        assert(r >= 0 && r <= 0.06);
    }
}