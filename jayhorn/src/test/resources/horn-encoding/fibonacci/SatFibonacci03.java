import java.util.Random;

public class SatFibonacci01 {

	static int fibonacci(int n) {
		if (n < 1) {
			return 0;
		} else if (n == 1) {
			return 1;
		} else {
			return fibonacci(n - 1) + fibonacci(n - 2);
		}
	}

	static void main(String[] args) {
		Random rand = new Random(42);

		int x = rand.nextInt();
		if (x > 46) {
			return;
		}
		int result = fibonacci(x);
		if (x < 9 || result >= 34) {
			return;
		} else {
			assert false;
		}
	}
}
