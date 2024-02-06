package jayhorn.hornify.encoder;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.lang.Math;
import java.math.MathContext;

import static java.lang.Math.pow;

public class IeeeFloatSpect {

    public int f;
    public int e;
    public IeeeFloatSpect() {
        this.f = 0;
        this.e = 0;
    }

    public IeeeFloatSpect(int f, int e) {
        this.f = f;
        this.e = e;
    }
    public int getF() {
        return f;
    }

    public void setF(int f) {
        this.f = f;
    }

    public int getE() {
        return e;
    }

    public void setE(int e) {
        this.e = e;
    }
    public BigInteger bias() {
        return new BigInteger("2").pow(e-1).subtract(BigInteger.ONE);

    }
    public int width()
    {
        return f + e + 1;
    }
   /* public floatbvTypet toType() {
        floatbvTypet result = new floatbvTypet();
        result.setF(f);
        result.setWidth(width());
        return result;
    }*/

    public BigInteger maxExponent() {
        return new BigInteger("2").pow(e-1).subtract(BigInteger.ONE);
    }

    public BigInteger maxFraction() {
        return new BigInteger("2").pow(f).subtract(BigInteger.ONE);
    }

   /* public IeeeFloatSpect(floatbvTypet type) {
        int width = type.getWidth();
        f = type.getF();
        assert f != 0;
        assert f < width;
        e = width - f - 1;
    }*/

   /* public IeeeFloatSpect(floatbvType2t type) {
        int width = type.getWidth();
        f = type.getFraction();
        assert f != 0;
        assert f < width;
        e = width - f - 1;
    }*/

   /* public Type2tc getType() {
        return new floatbvType2tc(f, e);
    }*/
    public boolean equals(IeeeFloatSpect other) {
        return f == other.f;
    }
}
