import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
	  float f = Verifier.nondetFloat();
	  double d;
	//C++ TO JAVA CONVERTER WARNING: Unsigned integer types have no direct equivalent in Java:
	//ORIGINAL LINE: unsigned char x = __VERIFIER_nondet_uchar();
	  byte x = (byte) Verifier.nondetChar();

	  d = f;

	  if (f == x)
	  {
		if (!(d == x))
		{
		 assert false;
		}
	  }
	}
}