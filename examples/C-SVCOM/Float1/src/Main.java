
public class Main
{

    public static void main(String[] args)
	{
	  double x;
	  int y;

	  x = 2.0;
	  x -= 0.6;
	  y = (int)x; // this yields 1.4, which is cut off

	  if (!(y == 1))
	  {
		  assert false;
	  }

	  x = 2.0;
	  x -= 0.4;
	  y = (int)x; // this yields 1.6, which is cut off, too!
		   // This is what the standard says!

	  if (!(y == 1))
	  {
		  assert false;
	  }
	}
}