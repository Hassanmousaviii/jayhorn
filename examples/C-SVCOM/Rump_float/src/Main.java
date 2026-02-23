public class Main {

	public static void main(String[] args)
	{
	  float x;
	  float y;
	  float r;
	  x = 77617.0f;
	  y = 33096.0f;
	  r = 333.75f * y * y * y * y * y * y + x * x * (11.0f * x * x * y * y - y * y * y * y * y * y - 121.0f * y * y * y * y - 2.0f) + 5.5f * y * y * y * y * y * y * y * y + x / (2.0f * y);

	  assert ((r >= 0.0f));

	}
}