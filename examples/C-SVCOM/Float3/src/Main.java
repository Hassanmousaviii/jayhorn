import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static double d = 0.0;

	public static void f1()
	{
	  d = 1.0;
	}

	public static void main(String[] args)
	{
	  int x = 2;

	  if (Verifier.nondetInt() != 0)
	  {
		x = 4;
	  }

	  f1();

	  d +=  (x == 2) ? 1.0 : 0.0;

	  d +=  (x > 3) ? 1.0 : 0.0;

	  if (!(d == 2.0))
	  {
		  assert false;
	  }
	}
}