import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
	  double d1 = Verifier.nondetDouble();
	  double _d1 = Verifier.nondetDouble();
	  d1 = _d1;

	  if (Double.isNaN(d1))
	  {
		  assert false;
	  }
	  if (Double.isInfinite(d1))
	  {
		  assert false;
	  }
	  if (!Double.isInfinite(d1))
	  {
		  assert false;
	  }

	  double d2 = Verifier.nondetDouble();
	  double _d2 = Verifier.nondetDouble();
	  d2 = _d2;
		Verifier.assume(Double.isInfinite(d2));
	 /* if (!(!isnormal(d2)))
	  {
		  assert false;
	  }*/
	  if (Double.isNaN(d2))
	  {
		  assert false;
	  }


	  double d3 = Verifier.nondetDouble();
	  double _d3 = Verifier.nondetDouble();
	  d3 = _d3;
		Verifier.assume(Double.isNaN(d3));
	
	  if (Double.isInfinite(d3))
	  {
		  assert false;
	  }
	  if (!(d3 != d3))
	  {
		  assert false;
	  }


	  double d4 = Verifier.nondetDouble();
	  double _d4 = Verifier.nondetDouble();
	  d4 = _d4;
		Verifier.assume(Double.isInfinite(d4));
	  if (d4 == Double.NaN)
	  {
		  assert false;
	  }
	  if (Double.isInfinite(d4))
	  {
		  assert false;
	  }


	  double d5 = Verifier.nondetDouble();
	  double _d5 = Verifier.nondetDouble();
	  d5 = _d5;
		Verifier.assume(!Double.isNaN(d5) && !Double.isInfinite(d5));
	  if (!Double.isInfinite(d5))
	  {
		  assert false;
	  }
	}
}