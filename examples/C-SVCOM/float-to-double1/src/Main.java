import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

   
    public static void main(String[] args) {
        float f = Float.NaN;//Verifier.nondetFloat();

        double d = (double) f;
        float ff = (float) d;

        if (!((f == ff) || (Float.isNaN(f) && Float.isNaN(ff)))) {
           assert false;
        }
    }
}