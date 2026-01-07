
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Double y = Verifier.nondetDouble();

			if (x >= y && 8.0 >= x) {
			    assert(8.0 >= y);
			}
	}
}
