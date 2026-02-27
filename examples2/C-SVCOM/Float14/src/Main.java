public class Main
{

	public static int Main()
	{
	  float temp;

	  temp = 1.8e307f + 1.5e50f; // should produce overflow -> +infinity (according to standard)
	  if (!(Float.isInfinite(temp)))
	  {
		assert false;
	  }

	  float x;

	  x = temp - temp;

	  // should be +inf
	  if (!(Float.isInfinite((temp))))
	  {
		 assert false;
	  }
	}
}