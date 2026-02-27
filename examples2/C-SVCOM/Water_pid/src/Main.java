import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {

	public static double yn = 0.0;

	public static double ui = 0.0;

	public static double y(int i)
	{
	  yn += ui;
	  return (double)yn;
	}

	public static void main(String[] args) {
	  double yi;
	  double yc;
	  double K;
	  double T;
	  double taui;
	  double taud;
	  double ei;
	  double sumej;
	  double epi;
	  int i;
	  T = 1.0;
	  taui = 1.0;
	  taud = 1.0;
	  K = .5;
	  yc = .5;
	  yi = y(0);
	  epi = yc - yi;
	  sumej = epi;
	  for (i = 0; i < 120; i++)
	  {
		yi = y(i);
		ei = yc - yi;
		sumej = sumej + ei;
		ui = K * (ei + sumej * T / taui + taud / T * (ei - epi));
		epi = ei;

		assert (epi >= -1.0 && epi <= 1.0);
	  }
	}
}