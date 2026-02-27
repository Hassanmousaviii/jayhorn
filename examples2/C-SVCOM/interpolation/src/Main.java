import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

    static float getMin(int i) {
        switch (i) {
            case 0: return 5f;
            case 1: return 10f;
            case 2: return 12f;
            case 3: return 30f;
            case 4: return 150f;
            default: throw new IllegalArgumentException("Invalid index for min");
        }
    }

    static float getMax(int i) {
        switch (i) {
            case 0: return 10f;
            case 1: return 12f;
            case 2: return 30f;
            case 3: return 150f;
            case 4: return 300f;
            default: throw new IllegalArgumentException("Invalid index for max");
        }
    }

    public static void main(String[] args) {
        float t = Verifier.nondetFloat();
        float z;
        int i;

        Verifier.assume(t >= getMin(0) && t <= getMax(4));

        for (i = 0; i < 5; i++) {
            if (t <= getMax(i)) break;
        }

        float min_i = getMin(i);
        float max_i = getMax(i);
        z = (t - min_i) / (max_i - min_i);

        assert(z >= 0.f && z <= 1.f);
    }
}