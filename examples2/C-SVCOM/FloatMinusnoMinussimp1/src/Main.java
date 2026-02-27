public class Main
{

	public static void main(String[] var0)
	{

	  int i;
	  int j;
	  double d;

	  i = (int)100.0;
	  d = (double) i;
	  j = (int)d;
	  if (!(j == 100))
	  {
		 assert false;
	  }
	}
}