
import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
	public static void main(String[] args) {
			Double x = 3.2;
			Double y = Verifier.nondetDouble();
			assert(y / 1.0 != 0  );
	}
}
