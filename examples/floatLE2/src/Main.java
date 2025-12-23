
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();

//			for (int i = 0; i < x + 2; i++){
//				x = x - 10;
//			}

			assert(x <= 0.0);
	}
}

//  p1(a , b) p2(a,b,c)