import org.sosy_lab.sv_benchmarks.Verifier;

public class Main {

	public static double PADE_2_2(double x)
	{
		return x / x;
	}

	public static void main(String[] args)
	{
		double a;
		double r;

		a = Verifier.nondetDouble();

		r =  PADE_2_2(a);

		assert (r >= 0);

	}
}