
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Verifier.assume(!Double.isNaN(x));
			assert   x <=  x +  1.0;
	}
}
