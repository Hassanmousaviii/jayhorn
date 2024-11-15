package jayhorn.solver.princess;
import jayhorn.solver.*;

public class PrincessTempFloatingPointADTFactory implements TempFloatingPointADTFactory {



    public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision) {
        return PrincessADT.mkADT(new String[]{precision == PrincessFloatingPointType.Precision.Single ? "ExtendedFloatingPoint" : "ExtendedDoubleFloatingPoint"},
                new String[]{precision == PrincessFloatingPointType.Precision.Single ? "ExtendedFloatingPoint" : "ExtendedDoubleFloatingPoint"},
                new int[]{
                        ADTTempType.ListADTTypeIndex
                },
                new ProverType[][]{{BoolType.INSTANCE, new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 9 : 12), new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 48 : 106),BoolType.INSTANCE, BoolType.INSTANCE,BoolType.INSTANCE,BoolType.INSTANCE}},
                new String[][]{{"esign", "eexponent", "emantissa","eisNan", "eisInfinity","eOVF","eUDF"}});
    }
}
