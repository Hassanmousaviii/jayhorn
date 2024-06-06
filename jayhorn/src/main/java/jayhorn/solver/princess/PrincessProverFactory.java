package jayhorn.solver.princess;

import jayhorn.solver.*;

public class PrincessProverFactory implements ProverFactory {

	private final StringADTFactory stringADTFactory;
	private final FloatingPointADTFactory floatingPointADTFactory;

	private final TempFloatingPointADTFactory tempFloatingPointADTFactory;

	private final TempFloatingPointOperandsADTFactory tempFloatingPointOperandsADTFactory;

	public PrincessProverFactory() {
		this.stringADTFactory = new PrincessStringADTFactory();
		this.floatingPointADTFactory = new PrincessFloatingPointADTFactory();
		this.tempFloatingPointADTFactory = new PrincessTempFloatingPointADTFactory();
		this.tempFloatingPointOperandsADTFactory = new PrincessTempFloatingPointOperandsADTFactory();
	}

	public PrincessProverFactory(StringADTFactory stringADTFactory, FloatingPointADTFactory floatingPointADTFactory, TempFloatingPointADTFactory tempFloatingPointADTFactory, TempFloatingPointOperandsADTFactory tempFloatingPointOperandsADTFactory) {
		this.stringADTFactory = stringADTFactory;
		this.floatingPointADTFactory = floatingPointADTFactory;
		this.tempFloatingPointADTFactory = tempFloatingPointADTFactory;
		this.tempFloatingPointOperandsADTFactory = tempFloatingPointOperandsADTFactory;
	}

	@Override
	public Prover spawn() {
		return new PrincessProver();
	}

	@Override
	public Prover spawnWithLog(String basename) {
		return new PrincessProver(basename);
	}

	@Override
	public ProverADT spawnStringADT() {
		return stringADTFactory.spawnStringADT();
	}

	@Override
	public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision) {
		return floatingPointADTFactory.spawnFloatingPointADT(precision);
	}
	@Override
	public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision)
	{
		return tempFloatingPointADTFactory.spawnTempFloatingPointADT(precision);
	}
	@Override
	public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT)
	{
		return tempFloatingPointOperandsADTFactory.spawnTempFloatingPointOperandsADT(precision, tempFloatingPointADT);
	}
}
