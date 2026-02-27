public class Main
{

	public static void main(String[] args)
	{
	  float a;
	  double b;

	  // various forms of floating-point literals
	  a = 1.25f;
	  if (!(a == 1.25f))
	  {
		  assert false;
	  }

	  b = 1.250;
	  if (!(b == 1.25))
	  {
		  assert false;
	  }

	  // with exponent
	  a = 0.5e2F;
	  if (!(a == 50.0f))
	  {
		  assert false;
	  }

	 
	}
}