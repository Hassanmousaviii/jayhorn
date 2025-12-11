package jayhorn.solver.spacer;

import com.microsoft.z3.Context;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointType;

public class SpacerTempFloatingPointOperandsADTFactory implements TempFloatingPointOperandsADTFactory {
    private final Context ctx;

    public SpacerTempFloatingPointOperandsADTFactory(Context ctx) {
        this.ctx = ctx;
    }



    @Override
    public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT) {
        boolean isSingle = (precision == PrincessFloatingPointType.Precision.Single);

        String typeName = isSingle ? "TempFloatingPointOperands" : "TempDoubleFloatingPointOperands";

        return SpacerADT.mkSimpleADT(
                ctx,
                typeName,
                typeName,
                new ProverType[]{
                        tempFloatingPointADT.getType(0),
                        tempFloatingPointADT.getType(0)
                },
                new String[]{"left", "right"}
        );
    }
}
