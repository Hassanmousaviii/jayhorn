public class Main {

    static boolean INIT1, INIT2;
    static float X, P;

    // For filter1
    static float E0 = 0.0f, E1 = 0.0f;
    static float S0 = 0.0f, S1 = 0.0f;

    // For filter2
    static float E20 = 0.0f, E21 = 0.0f;
    static float S20 = 0.0f, S21 = 0.0f;

  
    static void filter1() {
        if (INIT1) {
            S0 = X;
            P = X;
            E0 = X;
            E1 = 0.0f;
            S1 = 0.0f;
        } else {
            P = (float)(0.5 * X - 0.7 * E0 + 0.4 * E1 + 1.5 * S0 - 0.7 * S1);
            E1 = E0;
            E0 = X;
            S1 = S0;
            S0 = P;
            X = (float)(P / 6.0 + S1 / 5.0);
        }
    }

    static void filter2() {
        if (INIT2) {
            S20 = (float)(0.5 * X);
            P = X;
            E20 = (float)(0.8 * X);
            E21 = 0.0f;
            S21 = 0.0f;
        } else {
            P = (float)(0.3 * X - 0.2 * E20 + 1.4 * E21 + 0.5 * S20 - 1.7 * S21);
            E21 = (float)(0.5 * E20);
            E20 = (float)(2.0 * X);
            S21 = S20 + 10.0f;
            S20 = (float)(P / 2.0 + S21 / 3.0);
            X = (float)(P / 8.0 + S21 / 10.0);
        }
    }

    public static void main(String[] args) {
        X = 0.0f;
        INIT1 = true;
        INIT2 = true;

        while (X >= -1155.0f && X <= 4251.0f) {
            X = (float)(0.98 * X + 85.0);

            if (X >= -400.0f && X <= 400.0f) {
                filter1();
                X += 100.0f;
                INIT1 = false;
            } else if (X >= -800.0f && X <= 800.0f) {
                filter2();
                X -= 50.0f;
                INIT2 = false;
            }
        }
        assert false;
    }
}