package jayhorn.solver;

import jayhorn.solver.princess.PrincessFloatingPointType;

public interface FloatingPointADTFactory {
    public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision);
}
