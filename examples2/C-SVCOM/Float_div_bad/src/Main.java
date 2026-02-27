public class Main
{


	public static void main(String[] args)
	{
	  float x = 1.0f, X = 1.6F;
	  float x1 = x / X;

	  while (x1 != x)
	  {
		x = x1;
		x1 = x / X;
	  }

	  assert (x == 0.0F);

	}
}