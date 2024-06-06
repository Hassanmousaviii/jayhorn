package jayhorn.solver;

import jayhorn.solver.princess.PrincessFloatingPointType;

public interface TempFloatingPointOperandsADTFactory {
    public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT);
}
