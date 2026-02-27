import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

	public static final double Pi = 3.141592653589793238;

	public static double PADE_2_2(double x)
	{
	  double x_2 = x * x;
	  return 1.0 - x_2 / (3.0 + 9.0 / 5.0 * x_2);
	}

	public static double ARCTAN_0_1(double x)
	{
	  return x * PADE_2_2(x);
	}

	public static double ARCTAN_POS(double x)
	{
	  if (x > 1.0)
	  {
		  return 3.141592653589793238 / 2.0 - ARCTAN_0_1(1.0 / x);
	  }
	  else
	  {
		  return ARCTAN_0_1(x);
	  }
	}

	public static double ARCTAN(double x)
	{
	  if (x < 0.0)
	  {
		  return -ARCTAN_POS(-x);
	  }
	  else
	  {
		  return ARCTAN_POS(x);
	  }
	}

	public static void main(String[] args)
	{
	  double a;
	  double r;

	  a = Verifier.nondetDouble();
	  Verifier.assume(a >= -1.79e308 && a <= 1.79e308);

	  r = ARCTAN(a);

	 assert (r >= -1.571 && r <= 1.571);

	}
}