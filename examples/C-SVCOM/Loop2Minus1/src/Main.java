import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static float pi = 3.14159F;


	public static void main(String[] args)
	{
		float x = Verifier.nondetFloat();
		float octant = pi / 3;
		Verifier.assume(x > 0 && x < octant);
		float oddExp = x;
		float evenExp = 1.0F;
		float term = x;
	
		int count = 2;
		int multFactor = 0;
		int temp;

		while (true)
		{
			term = term * (x / count);
			multFactor = (count>>>1 % 2 == 0) ? 1 : -1;

			evenExp = evenExp + multFactor * term;

			count++;

			term = term * (x / count);

			oddExp = oddExp + multFactor * term;

			count++;

			temp = Verifier.nondetInt();
			if (temp == 0)
				break;
		}

		assert (oddExp >= evenExp);

	}
}