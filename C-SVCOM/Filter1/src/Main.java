
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{
	public static void main(String[] args)
	{
	  double E0;
	  double E1;
	  double S;
	  int i;

	  E1 = 0;
	  S = 0;

	  for (i = 0; i <= 1000000; i++)
	  {

		E0 = Verifier.nondetDouble();


		if (Verifier.nondetInt() != 0)
		{
		  S = 0;
		}
		else
		{
		  S = 0.999 * S + E0 - E1;
		}
		E1 = E0;

		assert (S >= -10000.0 && S <= 10000.0);
	  }

	}
}