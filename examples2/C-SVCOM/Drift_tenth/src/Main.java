public class Main
{
	public static void main(String[] args)
	{
	  float tick = 1.0f / 10.0f;
	  float time = 0.0f;
	  int i;

	  for (i = 0; i < 10; i++)
	  {
		time += tick;
	  }
	  assert (time != 1.0F);

	}
}