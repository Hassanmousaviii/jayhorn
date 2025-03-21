
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{


	public static void main(String[] args)
	{
	  int x;
	  float y;
	  float z;

	  x = Verifier.nondetInt();
		Verifier.assume(x >= -10 && x <= 10);

	  y = x * x - 2.0f;
	  assert (y != 0.0f);
	  z = 1.0f / y;

	}
}