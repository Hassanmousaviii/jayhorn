import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{
	public static double C1 = 4.16666666666666019037e-02;
	public static double C2 = -1.38888888888741095749e-03;
	public static double C3 = 2.48015872894767294178e-05;
	public static double C4 = -2.75573143513906633035e-07;
	public static double C5 = 2.08757232129817482790e-09;
	public static double C6 = -1.13596475577881948265e-11;

	public static double mcos(double x)
	{
	  double a;
	  double hz;
	  double z;
	  double r;
	  double qx;
	  double zr;
	  z = x * x;
	  if (x < 0.0)
	  {
		  x = -x;
	  }
	  hz = 0.5 * z;
	  r = z * (C1 + z * (C2 + z * (C3 + z * (C4 + z * (C5 + z * C6)))));
	  zr = z * r;
	  if (x < 0.3)
	  {
		return 1.0 - (hz - zr);
	  }
	  else
	  {
		if (x > 0.78125)
		{
		  qx = 0.28125;
		}
		else
		{
		  qx = x / 4.0;
		}
		hz = hz - qx;
		a = 1.0 - qx;
		return a - (hz - zr);
	  }
	}

	public static void main(String[] args)
	{
	 double a;
	 double r;

	  a = Verifier.nondetDouble();
	  Verifier.assume(a >= -0.5 && a <= 0.75);

	  r = mcos(a);

	  assert (r >= 0.0 && r <= 1.1);
	}
}