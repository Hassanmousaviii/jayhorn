import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static float pi = 3.14159F;


	public static void main(String[] args)
	{
		float x = Verifier.nondetFloat();
		float octant1 = 0F;
		float octant2 = pi / 8;
		Verifier.assume(x > octant1 && x < octant2);
		float oddExp = x;
		float evenExp = 1.0F;
		float term = x;

		int count = 2;
		int multFactor = 0;
		int temp;

		while (true)
		{
			term = term * (x / (float) count);
			multFactor = (count>>>1 % 2 == 0) ? 1 : -1;

			evenExp = evenExp + (float) multFactor * term;

			count++;

			term = term * (x / (float) count);

			oddExp = oddExp + multFactor * term;

			count++;

			temp = Verifier.nondetInt();
			if (temp == 0)
				break;
		}

		assert (evenExp >= oddExp);
	}
}