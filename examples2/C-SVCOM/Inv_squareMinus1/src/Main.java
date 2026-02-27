import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{


	public static void main(String[] args)
	{
	  float x;
	  float y;
	  float z;

	  x = Verifier.nondetFloat();
		Verifier.assume(x >= -1.0f && x <= 1.0f);

	  if (x != 0.0f)
	  {
		y = x * x;
		assert (y != 0.0f);
		z = 1.0f / y;
	  }

	}
}