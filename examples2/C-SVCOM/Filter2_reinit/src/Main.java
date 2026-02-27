import org.sosy_lab.sv_benchmarks.Verifier;

public class Main
{
	public static void main(String[] args)
	{
	  double E;
	  double E0;
	  double E1;
	  double S0;
	  double S1;
	  double S;
	  int i;

	  E = Verifier.nondetDouble();
	  E0 = Verifier.nondetDouble();
		Verifier.assume(E >= 0.0 && E <= 1.0);
		Verifier.assume(E0 >= 0.0 && E0 <= 1.0);

	  S0 = 0;
	  S = 0;

	  for (i = 0; i <= 1000000; i++)
	  {

		E1 = E0;
		E0 = E;

		E = Verifier.nondetDouble();
		  Verifier.assume(E >= 0.0 && E <= 1.0);

		if (Verifier.nondetInt() != 0)
		{
		  E1 = E;
		  E0 = E;
		  S0 = E;
		  S = E;
		}

		S1 = S0;
		S0 = S;
		S = 0.7 * E - E0 * 1.3 + E1 * 1.1 + S0 * 1.4 - S1 * 0.7;

		assert (S >= -4.0 && S <= 4.0);
	  }

	}
}