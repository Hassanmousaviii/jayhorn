package jayhorn.solver.princess;

import jayhorn.solver.BitVectorType;
import jayhorn.solver.ProverType;

public class PrincessFloatingPointType implements ProverType {

    BitVectorType sign, exponent, mantissa;
    public static enum Precision {Single, Double};

    public PrincessFloatingPointType(Precision precision )
    {
        sign = new BitVectorType(1);
        exponent = new BitVectorType(precision == Precision.Single ? 8 : 11);
        mantissa = new BitVectorType(precision == Precision.Single ? 23 : 53);
    }

}
