package jayhorn.solver;

import jayhorn.solver.princess.PrincessFloatingPointType;

public interface TempFloatingPointADTFactory {
    public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision);
}
