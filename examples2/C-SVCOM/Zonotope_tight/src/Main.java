import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

	public static void main(String[] args) {
	  double x;
	  double y;

	  x = Verifier.nondetDouble();
		Verifier.assume(x >= 0.0 && x <= 10.0);

	  y = x * x - x;
	  if (y >= 0)
	  {
		  y = x / 10.0;
	  }
	  else
	  {
		  y = x * x + 2.0;
	  }

	  assert (y >= 0.0 && y <= 4.0);

	}
}