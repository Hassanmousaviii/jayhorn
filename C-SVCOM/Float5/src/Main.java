import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{
	public static void main(String[] args)
	{
	  float a = Verifier.nondetFloat();
	  float b = Verifier.nondetFloat();

	  if (!(a == 1.0F || a == 0.5F || a == 2.0F || a == 3.0F || a == 0.1F))
	  {
		  return;
	  }
	  b = a;
	  a /= 2.0F;
	  a *= 2.0F;
	  if (!(a == b))
	  {
		 assert false;
	  }
	}
}