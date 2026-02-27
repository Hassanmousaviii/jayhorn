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

    public static void main(String[] agrs) {
        double x = Verifier.nondetDouble();
        double y;
        y = bessely0test(x);
        assert x < 1.25 || y > 0.2;
    }

    public static double bessely0test(double x) {
        if (x == 1.0) return 0.08825696421567698;
        if (x == 1.25) return 0.2582168515945408;
        if (x == 1.5) return 0.38244892379775897;
        if (x == 1.75) return 0.465492628646906;
        if (x == 2.0) return 0.5103756726497451;
        if (x == 2.25) return 0.5200647624572782;
        if (x == 2.5) return 0.49807035961523183;
        if (x == 2.75) return 0.4486587215691319;
        if (x == 3.0) return 0.3768500100127904;
        if (x == 3.25) return 0.2882869026730871;
        return 1.0;
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