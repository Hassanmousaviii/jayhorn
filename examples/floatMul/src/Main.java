
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Double y = Verifier.nondetDouble();
			assert(y * 1.0 != y);
	}
}

//  p1(a , b) p2(a,b,c)