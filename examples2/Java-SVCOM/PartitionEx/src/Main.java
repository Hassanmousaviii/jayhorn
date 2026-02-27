/*
 * Origin of the benchmark:
 *     license: MIT (see /java/jayhorn-recursive/LICENSE)
 *     repo: https://github.com/jayhorn/cav_experiments.git
 *     branch: master
 *     root directory: benchmarks/recursive
 * The benchmark was taken from the repo: 24 January 2018
 */
import org.sosy_lab.sv_benchmarks.Verifier;

import java.io.Console;
import java.math.BigInteger;
import java.math.BigDecimal;

public class Main {

    public static void runSymbolic(double y) {
        if (y > runConcrete(y)) {
//            System.out.println("greater than the input ");
            assert false;
        } else {
//            System.out.println("less than the input");
        }
    }

    public static double runConcrete(double z) {
        if (z == 10.0) {
            return z / 1.2;
        }
        return z * 1.2;
    }

    public static void main(String[] args) {
        double x = Verifier.nondetDouble();
        Verifier.assume(5.0 < x && x < 10.0);
        runSymbolic(x);
    }
    /*public static void main(String[] args) {

      // float a = Verifier.nondetFloat();
      // Verifier.assume(a == 0.1);
       //Verifier.assume(Double.isInfinite(a));

       // double a = 0.071;//Verifier.nondetDouble();
        // Verifier.assume(a == 0.1);
        //Verifier.assume(Double.isInfinite(a));

        *//*for(int i = 0; i < 9; ++i) {
            a += 0.0091;
        }*//*
        float a = Verifier.nondetFloat();
       // Verifier.assume(!Double.isNaN(a));
        //Verifier.assume(!Double.isInfinite(a));

        for (int i= 0; i < 5; i++)
            a /= 0.1F;

        assert (a != 10000.0F);

        //assert !Double.isInfinite(a * 0.0011);
    }*/

}