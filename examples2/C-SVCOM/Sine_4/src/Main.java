import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
		float IN = Verifier.nondetFloat(), VAL = 1.01F, HALFPI = 1.57079632679f;
		Verifier.assume(IN > -HALFPI && IN < HALFPI);

		float x = IN;

		float result = x - (x * x * x) / 6.0f + (x * x * x * x * x) / 120.0f + (x * x * x * x * x * x * x) / 5040.0f;

		if (!(result <= VAL && result >= -VAL))
		{
			assert false;
		}

	}
}