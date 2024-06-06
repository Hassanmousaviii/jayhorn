package jayhorn.solver;

import jayhorn.solver.princess.PrincessFloatingPointType;

public interface ProverFactory {

	public Prover spawn();

	public Prover spawnWithLog(String basename);

	public ProverADT spawnStringADT();

	public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision);

	public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision);
	public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT);

}
