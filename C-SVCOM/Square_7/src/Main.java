import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
		float IN = Verifier.nondetFloat(), VAL = 1.4F;
		Verifier.assume(IN >= 0.0f && IN < 1.0f);

		float x = IN;

		float result = 1.0f + 0.5f * x - 0.125f * x * x + 0.0625f * x * x * x - 0.0390625f * x * x * x * x;

		if (!(result >= 0.0f && result < VAL))
		{
			assert false;
		}

	 
	}
}