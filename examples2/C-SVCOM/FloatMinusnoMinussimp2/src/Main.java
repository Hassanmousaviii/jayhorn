
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
	  double f;
	  double f2;
	  f2 = Verifier.nondetDouble();
	  // the following rely on f not being a NaN
		Verifier.assume(!Double.isNaN(f2));
		Verifier.assume(Double.isInfinite(f2));
	  f = f2;

	  // addition
	  if (!(100.0 + 10.0 == 110.0))
	  {
		  assert false;
	  }
	  if (!(0.0 + f == f))
	  {
		  assert false;
	  }
	//  if(!(f+0==f)) {reach_error();abort();}
	  if (!(100.0 + 0.5 == 100.5))
	  {
		  assert false;
	  }
	//  if(!(0.0+0.0+f==f)) {reach_error();abort();}

	  // subtraction
	  if (!(100.0 - 10.0 == 90.0))
	  {
		  assert false;
	  }
	//  if(!(0-f==-f)) {reach_error();abort();}
	//  if(!(f-0==f)) {reach_error();abort();}
	  if (!(100.0 - 0.5 == 99.5))
	  {
		  assert false;
	  }
	//  if(!(0.0-0.0-f==-f)) {reach_error();abort();}

	  // unary minus
	  if (!(-(-100.0) == 100.0))
	  {
		  assert false;
	  }
	  if (!(-(1.0 - 2.0) == 1.0))
	  {
		  assert false;
	  }
	  if (!(-(-f) == f))
	  {
		  assert false;
	  }

	  // multiplication
	  if (!(100.0 * 10.0 == 1000.0))
	  {
		  assert false;
	  }
	  if (!(0.0 * f == 0.0))
	  {
		  assert false;
	  }
	  if (!(f * 0.0 == 0.0))
	  {
		  assert false;
	  }
	  if (!(100.0 * 0.5 == 50.0))
	  {
		  assert false;
	  }
	  if (!(f * 1.0 == f))
	  {
		  assert false;
	  }
	//  if(!(1*f==f)) {reach_error();abort();}
	//  if(!(1.0*1.0*f==f)) {reach_error();abort();}

	  // division
	  if (!(100.0 / 1.0 == 100.0))
	  {
		  assert false;
	  }
	  if (!(100.1 / 1.0 == 100.1))
	  {
		  assert false;
	  }
	  if (!(100.0 / 2.0 == 50.0))
	  {
		  assert false;
	  }
	  if (!(100.0 / 0.5 == 200.0))
	  {
		  assert false;
	  }
	  if (!(0.0 / 1.0 == 0.0))
	  {
		  assert false;
	  }
	  if (!(f / 1.0 == f))
	  {
		  assert false;
	  }

	  // conversion
	  if (!(((double)(float)100) == 100.0))
	  {
		  assert false;
	  }
	  if ((100.0) == 0.0)
	  {
		  assert false;
	  }

	  if (!((int)0.5 == 0))
	  {
		  assert false;
	  }
	  if (!((int)0.49 == 0.0))
	  {
		  assert false;
	  }
	  if (!((int)-1.5 == -1.0))
	  {
		  assert false;
	  }
	  if (!((int)-10.49 == -10))
	  {
		  assert false;
	  }

	  // relations
	  if (!(1.0 < 2.5))
	  {
		  assert false;
	  }
	  if (!(1.0 <= 2.5))
	  {
		  assert false;
	  }
	  if (!(1.01 <= 1.01))
	  {
		  assert false;
	  }
	  if (!(2.5 > 1.0))
	  {
		  assert false;
	  }
	  if (!(2.5 >= 1.0))
	  {
		  assert false;
	  }
	  if (!(1.01 >= 1.01))
	  {
		  assert false;
	  }
	  if (!(!(1.0 >= 2.5)))
	  {
		  assert false;
	  }
	  if (!(!(1.0 > 2.5)))
	  {
		  assert false;
	  }
	  if (!(1.0 != 2.5))
	  {
		  assert false;
	  }
	}
}