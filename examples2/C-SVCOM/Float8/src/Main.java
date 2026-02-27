import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
	  double d;
	  double q;
	  double r;
	  q = Verifier.nondetDouble();
	  Verifier.assume(Double.isInfinite(q));
	  d = q;
	  r = d + 0.0;
	  if (!(r == d))
	  {
		  assert false;
	  }
	}
}