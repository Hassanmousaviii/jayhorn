public class Main {

	public static void main(String[] args) {
		{
			float x;
			float y;
			float z;

			x = 1.0f;
			y = 1e7F;
			z = 42.0f;

			while (x < y) {
				x = x + 1.0f;
				y = y - 1.0f;
				z = z + 1.0f;
			}

			assert (z >= 0.0f && z <= 1e8);
		}
	}
}