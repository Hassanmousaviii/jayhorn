
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Double y = Verifier.nondetDouble();
			if (2.0 < y < 100.0 ){
				assert(x < x + y);
			}
	}
}

