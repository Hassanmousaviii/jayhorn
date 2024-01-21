package jayhorn.hornify.encoder;

import jayhorn.solver.FloatingPointADTFactory;
import jayhorn.solver.Prover;
import jayhorn.solver.ProverADT;

public class FloatingPointEncoder {

    public enum Precision{
        Single,
        Double
    }
    private Prover p;
    private ProverADT floatingPointADT;

    private Precision floatingPointPrecision;

    public FloatingPointEncoder(Prover p, ProverADT floatingPointADT, Precision precision)
    {
        this.p = p;
        this.floatingPointADT = floatingPointADT;
        this.floatingPointPrecision = precision;
    }
}
