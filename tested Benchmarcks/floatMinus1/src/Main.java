
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Double y = Verifier.nondetDouble();
			Verifier.assume(!Double.isNaN(x));
			Verifier.assume(!Double.isNaN(y));
			for (; x > y; x = x - 123.4){
				;
			}

			assert x - y <= 0.0;
	}
}
