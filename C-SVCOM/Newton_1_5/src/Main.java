import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static float f(float x)
	{
	  return x - (x * x * x) / 6.0f + (x * x * x * x * x) / 120.0f + (x * x * x * x * x * x * x) / 5040.0f;
	}

	public static float fp(float x)
	{
	  return 1 - (x * x) / 2.0f + (x * x * x * x) / 24.0f + (x * x * x * x * x * x) / 720.0f;
	}

	public static void main(String[] args)
	{
	  float IN = Verifier.nondetFloat(), VAL = 1.0F;
	  Verifier.assume(IN > -VAL && IN < VAL);

	  float x = IN - f(IN) / fp(IN);
	
	  x = x - f(x) / fp(x);


	  if (!(x < 0.1F))
	  {
			assert false;
	  }

	}
}