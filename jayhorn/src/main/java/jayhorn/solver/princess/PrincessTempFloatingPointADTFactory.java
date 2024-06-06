package jayhorn.solver.princess;
import jayhorn.solver.*;

public class PrincessTempFloatingPointADTFactory implements TempFloatingPointADTFactory {



    public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision) {
        return PrincessADT.mkADT(new String[]{precision == PrincessFloatingPointType.Precision.Single ? "TempFloatingPoint" : "TempDoubleFloatingPoint"},
                new String[]{precision == PrincessFloatingPointType.Precision.Single ? "TempFloatingPoint" : "TempDoubleFloatingPoint"},
                new int[]{
                        ADTTempType.ListADTTypeIndex
                },
                new ProverType[][]{{BoolType.INSTANCE, new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 8 : 11), new BitVectorType(precision == PrincessFloatingPointType.Precision.Single ? 25 : 55),BoolType.INSTANCE, BoolType.INSTANCE}},
                new String[][]{{"sign", "exponent", "mantissa","isNan", "isInfinity"}});
    }
}
