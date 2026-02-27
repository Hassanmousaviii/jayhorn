public class Main {

   
    // Helper method to get the raw int bits of a float, similar to union mix
    static int floatToRawIntBits(float f) {
        return Float.floatToRawIntBits(f);
    }

    // The f00 function translated to Java
    static int f00(float a, float b) {
        float sum = a + b;
        int bits = floatToRawIntBits(sum);
        // 0x80000000 is the bit pattern for -0.0f in IEEE 754 float
        if (!(bits != 0x80000000)) {
            assert false;
        }
        return 1;
    }

    public static void main(String[] args) {
        
 
        float a = -3.05993664e8f;
        float b = 3.05993664e8f;

        f00(a, b);
    }
}