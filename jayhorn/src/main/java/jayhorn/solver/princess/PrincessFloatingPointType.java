package jayhorn.solver.princess;

import jayhorn.solver.BitVectorType;
import jayhorn.solver.BoolType;
import jayhorn.solver.ProverType;

public class PrincessFloatingPointType implements ProverType {

   // BoolType sign, isNan, isInfinity;
   // BitVectorType  exponent, mantissa;
   public static enum Precision {Single, Double};

    public PrincessFloatingPointType( )
    {
        /*sign =  BoolType.INSTANCE;
        isNan = BoolType.INSTANCE;
        isInfinity = BoolType.INSTANCE;// new BitVectorType(1);
        exponent = new BitVectorType(precision == Precision.Single ? 8 : 11);
        mantissa = new BitVectorType(precision == Precision.Single ? 23 : 53);*/
    }

}
