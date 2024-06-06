package jayhorn.solver.princess;
import jayhorn.solver.*;

public class PrincessTempFloatingPointOperandsADTFactory implements TempFloatingPointOperandsADTFactory {


    private static final int TempFloatingPointADTTypeIndex = ADTTempType.TempFloatingPointADTTypeIndex;
    private static final int TempDoubleFloatingPointADTTypeIndex = ADTTempType.TempDoubleFloatingPointADTTypeIndex;
    public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT) {
        return PrincessADT.mkADT(new String[]{precision == PrincessFloatingPointType.Precision.Single ? "TempFloatingPointOperands" : "TempDoubleFloatingPointOperands"},
                new String[]{precision == PrincessFloatingPointType.Precision.Single ? "TempFloatingPointOperands" : "TempDoubleFloatingPointOperands"},
                new int[]{ADTTempType.ListADTTypeIndex},
                new ProverType[][]{{
                    tempFloatingPointADT.getType(0),tempFloatingPointADT.getType(0)
                }},
                new String[][]{{"left", "right"}});
    }
}
