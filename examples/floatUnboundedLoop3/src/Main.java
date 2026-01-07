
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = -4.0;
			x -= 2.0;
			x += 109.9;
			while (Verifier.nondetBoolean()) x++;

			assert (x != -1.0);
	}
}
