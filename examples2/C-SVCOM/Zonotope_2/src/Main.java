
public class Main {

	public static void main(String[] args) {
	  float x = 12.0f;
	  float x1 = 12.0f;
	  float y = 16.0f;
	  float y1 = 16.0f;
	  int i;
	  for (i = 0; i < 100000; i++)
	  {
		x = x1;
		y = y1;
		x1 = 3.0f * x / 4.0f + y / 4.0f;
		y1 = x / 4.0f + 3.0f * y / 4.0f;

		assert (x1 >= 0.0f && x1 <= 100.0f);
		assert (y1 >= 0.0f && y1 <= 100.0f);
	  }

	  assert (x1 - y1 >= -0.1f && x1 - y1 <= 0.1f);

	}
}