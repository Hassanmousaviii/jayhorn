public class Main {

	public static void main(String[] args) {
	  float x;
	  float y;
	  float z;
	  float r;

	  x = 1e7f;
	  y = x + 1.0f;
	  z = x - 1.0f;
	  r = y - z;

	  assert(r == 2.0f);
	}
}