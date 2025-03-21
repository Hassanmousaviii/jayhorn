import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {


	public static float f(float x)
	{
	  return 2.0f * x - 3.0f;
	}

	public static float g(float x)
	{
	  return -x + 5.0f;
	}

	public static void main(String[] args)
	{
	  int i;
	  float x;
	  float y;
	  float z;
	  float t;
	  float u;
	  float v;
	  y = f(0.0f);
	  z = g(0.0f);
	  u = f(.75f);
	  v = g(.25f);

	  for (i = 1; i <= 100000; i++)
	  {

		x = Verifier.nondetFloat();
		  Verifier.assume(x >= 0.0f && x <= (float)i / 100000.0f);

		y = f(x);
		z = g(x);
		u = f(v);
		v = g(u) / 2.0f;
	  }

	  t = y + 2.0f * z;
	  assert (t >= 6.9f && t <= 7.1f);

	}
}