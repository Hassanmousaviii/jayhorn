public class Main {

   
    public static void main(String[] args) {
        double x = 1.0;
        double x1 = x / 1.6;

        while (true) {
            if (x1 != x) {
                x = x1;
                x1 = x / 1.6;
            } else {
                boolean cond = (x == 0.0);
                assert(cond);
            }
        }
    }
}