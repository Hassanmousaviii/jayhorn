import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void f00(float f)
	{

	  if (f > 0x1.fffffeP+127f)
	  {
		if (!Float.isInfinite(f))
		{
			assert false;
		}
	  }
	}


	public static void main(String[] args)
	{

	  float f = Verifier.nondetFloat();

	  f00(f);


	}
}