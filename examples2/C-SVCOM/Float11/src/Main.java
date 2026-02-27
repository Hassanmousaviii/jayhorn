import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
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

	  // same flipped
	  if (!(-1.0 > -2.5))
	  {
		  assert false;
	  }
	  if (!(-1.0 >= -2.5))
	  {
		  assert false;
	  }
	  if (!(-1.01 >= -1.01))
	  {
		  assert false;
	  }
	  if (!(-2.5 < -1.0))
	  {
		  assert false;
	  }
	  if (!(-2.5 <= -1.0))
	  {
		  assert false;
	  }
	  if (!(-1.01 <= -1.01))
	  {
		  assert false;
	  }
	  if (!(!(-1.0 <= -2.5)))
	  {
		  assert false;
	  }
	  if (!(!(-1.0 < -2.5)))
	  {
		  assert false;
	  }
	  if (!(-1.0 != -2.5))
	  {
		  assert false;
	  }

	  // involving zero
	  if ((-1.0 < 0.0) == false)
	  {
		  assert false;
	  }
	  if (!(0.0 > -1.0))
	  {
		  assert false;
	  }
	  if (!(0.0 == -0.0))
	  {
		  assert false;
	  }
	  if (!(0.0 >= -0.0))
	  {
		  assert false;
	  }
	  if (!(1.0 > 0.0))
	  {
		  assert false;
	  }
	  if (!(0.0 < 1.0))
	  {
		  assert false;
	  }
	  if (!(1.0 > -0.0))
	  {
		  assert false;
	  }
	  if ((-0.0 < 1.0) == false)
	  {
		  assert false;
	  }

	  if (!(!(0.999f < 0.0f)))
	  {
		  assert false;
	  }
	  if (!(!(-0.999f > -0.0f)))
	  {
		  assert false;
	  }
	  if (!(!(0.999f <= 0.0f)))
	  {
		  assert false;
	  }
	  if (!(!(-0.999f >= -0.0f)))
	  {
		  assert false;
	  }
	}
}