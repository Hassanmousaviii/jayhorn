package jayhorn.hornify.encoder;

import java.io.Console;
import java.math.BigInteger;
import java.util.BitSet;
import java.util.Map;

public class IeeeFloatTest {
   // @Test
    public void ieeeFloatCanHandleOne() {
        BigInteger one = BigInteger.valueOf(1);
        double dOne = -0.30000000000000004;
        IeeeFloatt ieeeOne = new IeeeFloatt(new IeeeFloatSpect(52, 11));

        // Basic context
       /* Double.is
        assertTrue(Double.isNormal(dOne));*/

        // From double
        ieeeOne.fromDouble(dOne);
        //String frac =ieeeOne.get_fraction().toString(2);
//byte [] b = ieeeOne.get_fraction().toByteArray();
        //assert ieeeOne.toDouble() == dOne;
       /* assertAll(
                () -> assertEquals(ieeeOne.getExponent(), *//* captured value *//*),
                () -> assertEquals(ieeeOne.getFraction(), *//* captured value *//*),
                () -> assertEquals(ieeeOne.getSign(), *//* captured value *//*)
        );
        assertTrue(Double.isNormal(ieeeOne.toDouble()));*/

        // From integer
        ieeeOne.fromInteger(one);
        /*assertAll(
                () -> assertEquals(ieeeOne.getExponent(), *//* captured value *//*),
                () -> assertEquals(ieeeOne.getFraction(), *//* captured value *//*),
                () -> assertEquals(ieeeOne.getSign(), *//* captured value *//*)
        );
        assertTrue(Double.isNormal(ieeeOne.toDouble()));*/
    }
    public static BitSet bigIntToBitSet(BigInteger i) {

        return BitSet.valueOf(i.toByteArray());//.fromByteArray(i.toByteArray());
    }
    public static BitSet fromByteArray(byte[] bytes) {
        BitSet bits = new BitSet();
        for (int i = 0; i < bytes.length * 8; i++) {
            if ((bytes[bytes.length - i / 8 - 1] & (1 << (i % 8))) > 0) {
                bits.set(i);
            }
        }
        return bits;
    }
    public static byte[] toByteArray(BitSet bits) {
        byte[] bytes = new byte[bits.length() / 8 + 1];
        for (int i = 0; i < bits.length(); i++) {
            if (bits.get(i)) {
                bytes[bytes.length - i / 8 - 1] |= 1 << (i % 8);
            }
        }
        return bytes;
    }
}
