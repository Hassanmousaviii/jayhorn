import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{
	public static void main(String[] args) {
		// constants
		if (!(1.0 != 2.0)) {
			assert false;
		}
		if (!(1.0 == 1.0)) {
			assert false;
		}
		if (!(1.0 < 2.0)) {
			assert false;
		}
		if (!(!(-1.0 < -2.0))) {
			assert false;
		}
		if (!(2.0 > 1.0)) {
			assert false;
		}
		if (!(!(-2.0 > -1.0))) {
			assert false;
		}
		if (!(!(2.0 < 2.0))) {
			assert false;
		}
		if (!(!(-2.0 < -2.0))) {
			assert false;
		}
		if (!(!(2.0 > 2.0))) {
			assert false;
		}
		if (!(!(-2.0 > -2.0))) {
			assert false;
		}
		if (!(2.0 <= 2.0)) {
			assert false;
		}
		if (!(-2.0 <= -2.0)) {
			assert false;
		}
		if (!(2.0 >= 2.0)) {
			assert false;
		}
		if (!(-2.0 >= -2.0)) {
			assert false;
		}
		if (!(1.0 <= 2.0)) {
			assert false;
		}
		if (!(!(-1.0 <= -2.0))) {
			assert false;
		}
		if (!(2.0 >= 1.0)) {
			assert false;
		}
		if (!(!(-2.0 >= -1.0))) {
			assert false;
		}

		// variables
		float a = Verifier.nondetFloat();
		float b = Verifier.nondetFloat();
		if (!(a == 1.0f && b == 2.0f)) {
			return;
		}

		if (!(a != b)) {
			assert false;
		}
		if (!(a == a)) {
			assert false;
		}
		if (!(a < b)) {
			assert false;
		}
		if (!(!(-a < -b))) {
			assert false;
		}
		if (!(b > a)) {
			assert false;
		}
		if (!(!(-b > -a))) {
			assert false;
		}
		if (!(!(b < b))) {
			assert false;
		}
		if (!(!(-b < -b))) {
			assert false;
		}
		if (!(!(b > b))) {
			assert false;
		}
		if (!(!(-b > -b))) {
			assert false;
		}
		if (!(b <= b)) {
			assert false;
		}
		if (!(-b <= -b)) {
			assert false;
		}
		if (!(b >= b)) {
			assert false;
		}
		if (!(-b >= -b)) {
			assert false;
		}
		if (!(a <= b)) {
			assert false;
		}
		if (!(!(-a <= -b))) {
			assert false;
		}
		if (!(b >= a)) {
			assert false;
		}
		if (!(!(-b >= -a))) {
			assert false;
		}
	}
}