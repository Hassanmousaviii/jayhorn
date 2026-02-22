package jayhorn.solver.spacer;

import com.microsoft.z3.Context;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointType;

public class SpacerTempFloatingPointADTFactory implements TempFloatingPointADTFactory {

    private final Context ctx;

    /**
     * Constructor that takes a Context from SpacerProver
     * @param ctx Z3 Context instance
     */
    public SpacerTempFloatingPointADTFactory(Context ctx) {
        this.ctx = ctx;
    }


    @Override
    public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision) {
        boolean isSingle = (precision == PrincessFloatingPointType.Precision.Single);
        int exponentWidth = isSingle ? 9 : 12;
        int mantissaWidth = isSingle ? 72 : 159; // TODO: recheck

        ProverType exponentType = new BitVectorType(exponentWidth);
        ProverType mantissaType = new BitVectorType(mantissaWidth);


        String typeName = isSingle ? "ExtendedFloatingPoint" : "ExtendedDoubleFloatingPoint";

        return SpacerADT.mkSimpleADT(
                ctx,
                typeName,
                typeName,
                new ProverType[]{
                        BoolType.INSTANCE,    // sign
                        exponentType,         // exponent
                        mantissaType,         // mantissa
                        BoolType.INSTANCE,    // isNan
                        BoolType.INSTANCE,    // isInfinity
                        BoolType.INSTANCE,    // OVF (overflow)
                        BoolType.INSTANCE     // UDF (underflow)
                },
                new String[]{"esign", "eexponent", "emantissa", "eisNan", "eisInfinity", "eOVF", "eUDF"}
        );
    }
}
