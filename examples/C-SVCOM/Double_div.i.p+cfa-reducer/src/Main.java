public class Main {

    

    public static void main(String[] args) {
        double x = 1.0;
        double x1 = x / 2.5;

        while (true) {
            if (x1 != x) {
                x = x1;
                x1 = x / 2.5;
            } else {
                boolean cond = (x == 0.0);
                assert(cond);
            }
        }
    }
}