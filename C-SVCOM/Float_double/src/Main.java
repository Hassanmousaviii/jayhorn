public class Main
{


	public static void main(String[] args)
	{
	  double x = 1e20 + 1.0;
	  float y = (float) x;
	  assert (x != y);

	}
}