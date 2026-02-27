
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Verifier.assume( x >= 0);
			while (Verifier.nondetBoolean()) x++;

			assert (x != -1.0);
	}
}
