import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

	public static double _EPS = 1e-6;

	public static double SqrtR(double Input)
	{
	  double xn;
	  double xnp1;
	  double residu;
	  double lsup;
	  double linf;
	  int i;
	  Boolean cond;
	  if (Input <= 1.0)
	  {
		  xn = 1.0;
	  }
	  else
	  {
		  xn = 1.0 / Input;
	  }
	  xnp1 = xn;
	  residu = 2.0 * _EPS * (xn + xnp1);
	  lsup = _EPS * (xn + xnp1);
	  linf = -lsup;
	  cond = ((residu > lsup) || (residu < linf));
	  i = 0;
	  while (cond != false)
	  {
		xnp1 = xn * (15.0 + Input * xn * xn * (-10.0 + 3.0 * Input * xn * xn)) / 8.0;
		residu = 2.0 * (xnp1 - xn);
		xn = xnp1;
		lsup = _EPS * (xn + xnp1);
		linf = -lsup;
		cond = ((residu > lsup) || (residu < linf));
		i++;
	  }
	  return 1.0 / xnp1;
	}

	public static void main(String[] args) {
	  double d;
	  double dd;
	  double r;
	  double epsilon = 1e-8;

	  for (d = 1.0; d <= 20.0; d++)
	  {

		dd = Verifier.nondetDouble();
		  Verifier.assume(dd >= d - epsilon && dd <= d + epsilon);

		r = SqrtR(dd);

		assert (r >= 0.9 && r <= 5.0);
	  }

	}
}