
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {	
	
			Double x = Verifier.nondetDouble();
			Double y = Verifier.nondetDouble();
			Double z = Verifier.nondetDouble();

			if (x < y && y < z)
				assert(x < z );
	}
}

//  p1(a , b) p2(a,b,c)