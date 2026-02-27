
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {

		float f = Verifier.nondetFloat();

		double d = f;

		if (1.0D < d) {
			assert false;
		}
	}
}

