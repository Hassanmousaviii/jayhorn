package jayhorn.solver.princess;
import jayhorn.solver.*;

public class PrincessFloatingPointADTFactory implements FloatingPointADTFactory {



    public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision) {
        return PrincessADT.mkADT(new String[]{precision == PrincessFloatingPointType.Precision.Single ? "FloatingPoint" : "DoubleFloatingPoint"},
                new String[]{precision == PrincessFloatingPointType.Precision.Single ? "FloatingPoint" : "DoubleFloatingPoint"},
                new int[]{
                        ADTTempType.ListADTTypeIndex
                },
                new ProverType[][]{{BoolType.INSTANCE, new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 8 : 11), new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 23 : 53),BoolType.INSTANCE, BoolType.INSTANCE}},
                new String[][]{{"sign", "exponent", "mantissa","isNan", "isInfinity"}});
    }
}
