public class Main {

	public static void main(String[] args)
	{
	  double x0;
	  double x1;
	  double x2;
	  int i;

	  x0 = 11.0 / 2.0;
	  x1 = 61.0 / 11.0;
	  for (i = 0; i < 100; i++)
	  {
		x2 = 111.0 - (1130.0 - 3000.0 / x0) / x1;
		x0 = x1;
		x1 = x2;
	  }

	  assert (x0 >= 99.0 && x0 <= 101.0);

	}
}