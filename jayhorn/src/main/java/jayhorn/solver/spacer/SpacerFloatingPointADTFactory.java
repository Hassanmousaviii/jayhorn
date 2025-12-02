package jayhorn.solver.spacer;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointType;

public class SpacerFloatingPointADTFactory implements FloatingPointADTFactory {



    public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision) {
        return SpacerADT.mkADT(new String[]{precision == PrincessFloatingPointType.Precision.Single ? "FloatingPoint" : "DoubleFloatingPoint"},
                new String[]{precision == PrincessFloatingPointType.Precision.Single ? "FloatingPoint" : "DoubleFloatingPoint"},
                new int[]{
                        ADTTempType.ListADTTypeIndex
                },
                new ProverType[][]{{BoolType.INSTANCE, new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 8 : 11), new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 24 : 53),BoolType.INSTANCE, BoolType.INSTANCE,BoolType.INSTANCE,BoolType.INSTANCE}},
                new String[][]{{"sign", "exponent", "mantissa","isNan", "isInfinity","OVF","UDF"}});
    }
}
