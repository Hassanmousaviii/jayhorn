import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    static int e; // static variable to hold exponent

  
    static float FABS(float d) {
        return (d >= 0.f) ? d : -d;
    }

    static float FREXP(float d) {
        int x;
        float r;
        float dd = FABS(d);

        if (dd >= 1.f) {
            x = 1;
            r = 2.f;
            while (r <= dd) {
                x++;
                r = r * 2.f;
            }
        } else {
            x = 0;
            r = 0.5f;
            while (r > dd) {
                x--;
                r = r / 2.f;
            }
            r = r * 2.f;
        }

        e = x; // Assign to static variable instead of array
        return dd / r;
    }

    static float LDEXP(float d, int e) {
        float x = 1.0f;

        if (e >= 0) {
            while (e > 0) {
                e--;
                x = x * 2.f;
            }
        } else {
            while (e < 0) {
                e++;
                x = x / 2.f;
            }
        }

        return d * x;
    }

    public static void main(String[] args) {
        float a, b, c;

        a = Verifier.nondetFloat();
         Verifier.assume(a >= 1e-10f && a <= 1e10f);

        b = FREXP(a);          // e is assigned internally
        c = LDEXP(b, e / 2);   // use static e

        assert(c >= 0.f && c <= 1e6f);
    }
}