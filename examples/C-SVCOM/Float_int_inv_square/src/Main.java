import org.sosy_lab.sv_benchmarks.Verifier;
public class Main {
 public static void main(String[] args)
{
  int x;
  float y, z;

  x = Verifier.nondetInt();
  Verifier.assume(x >= -10 && x <= 10);

  y = x*x - 4.f;
  assert(y != 0.f);
  z = 1.f / y;
}
}
