package jayhorn.hornify.encoder;

import com.sun.org.apache.xpath.internal.operations.Bool;
import jayhorn.solver.*;
import scala.Int;

import javax.annotation.Nullable;
import java.math.BigInteger;

public class FloatingPointEncoder {

    public enum Precision{
        Single,
        Double
    }
    private Prover p;
    private ProverADT floatingPointADT;

    private Precision floatingPointPrecision;

    private int f, e;

    public FloatingPointEncoder(Prover p, ProverADT floatingPointADT, Precision precision)
    {
        this.p = p;
        this.floatingPointADT = floatingPointADT;
        this.floatingPointPrecision = precision;
        e = (precision == Precision.Single ? 8 : 11);
        f = (precision == Precision.Single ? 23 : 53);
    }
    public ProverExpr mkDoublePE(@Nullable Double value) {
        if( value != null)
            return mkDoublePEFromValue(value, floatingPointADT);

        return new ProverExpr() {
            @Override
            public ProverType getType() {
                return null;
            }

            @Override
            public BigInteger getIntLiteralValue() {
                return null;
            }

            @Override
            public boolean getBooleanLiteralValue() {
                return false;
            }
        };
    }
    private ProverExpr BVLit(BigInteger value, int bitLength)
    {
        return  p.mkBVLiteral(value, bitLength);
    }
    private ProverExpr mkDoublePEFromValue(double value, ProverADT floatingPointADT)
    {
        ProverExpr sign, exponent,mantissa;

        IeeeFloatt ieeeOne = new IeeeFloatt(new IeeeFloatSpect(f, e));
        ieeeOne.fromDouble(value);
        sign = BVLit( new BigInteger(ieeeOne.get_sign() ? "1" : "0"),1);
        exponent = BVLit(ieeeOne.get_exponent(),e);
        mantissa = BVLit(ieeeOne.get_fraction(),f);

        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa });

        return  res;
    }
}
