
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();

			if (x <= 0.0)

				assert(x <= 1.0);
	}
}
