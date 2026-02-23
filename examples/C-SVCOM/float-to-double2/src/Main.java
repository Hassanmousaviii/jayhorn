public class Main
{

	  public static void main(String[] args)
	{
	  float f = -0x1.0p-127f;
	  double d = -0x1.0p-127;
	  double fp = (double)f;

	  if (!(d == fp))
	  {
		  assert false;
	  }


	}
}