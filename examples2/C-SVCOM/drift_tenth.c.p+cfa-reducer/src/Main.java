import org.sosy_lab.sv_benchmarks.Verifier;
public class Main
{

	public static void main(String[] args)
	{
		float main__tick = 0.10000000149011612F;
        float main__time = 0.0F;
        int main__i;
        main__i = 0;
		while(main__i < 10)
		{
			main__time = main__time + main__tick;
			main__i = main__i + 1;
		}
		boolean __tmp_1 = (main__time != 1.0F);
		if(__tmp_1 == false)
			assert false;

	}
}