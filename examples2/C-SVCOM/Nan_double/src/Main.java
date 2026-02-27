import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {


	public static void main(String[] args)
	{
	  double x;
	  x = Verifier.nondetDouble();

	  assert (x == x);

	}
}