import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{


	public static double sqrt2 = 1.414213538169860839843750;

	public static void main(String[] args)
	{
	  double S;
	  double I;

	  I = Verifier.nondetDouble();
	  Verifier.assume(I >= 1.0 && I <= 3.0);

	  if (I >= 2.0)
	  {
		  S = sqrt2 * (1.0 + (I / 2.0 - 1.0) * (.5 - 0.125 * (I / 2.0 - 1.0)));
	  }
	  else
	  {
		  S = 1.0 + (I - 1.0) * (.5 + (I - 1.0) * (-.125 + (I - 1.0) * .0625));
	  }

	  assert(S >= 1.0 && S <= 2.0);
	
	}
}