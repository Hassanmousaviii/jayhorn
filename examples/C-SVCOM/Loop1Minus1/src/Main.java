import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{
	public static void main(String[] args)
	{
		float x = Verifier.nondetFloat();;
		Verifier.assume(x > -1.0);
		Verifier.assume(x < 1.0);
		float exp = 1.0F;
		float term = 1.0F;

		int count = 1;
		float result = 2 * (1 / (1 - x));
		int temp;

		while (true)
		{
			term = term * (x / count);
			exp = exp + term;
			count++;

			temp = Verifier.nondetInt();
			if (temp == 0)
				break;
		}

		assert (result >= exp);

	}
}