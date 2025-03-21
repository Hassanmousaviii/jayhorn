public class Main {

	public static void main(String[] args) {

	  double x;
	  double y;
	  double z;
	  double r;

	  x = 1e8;
	  y = x + 1;
	  z = x - 1;
	  r = y - z;

	  assert r == 2.0;
	}
}