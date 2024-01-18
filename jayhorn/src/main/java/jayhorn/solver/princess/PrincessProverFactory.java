package jayhorn.solver.princess;

import jayhorn.solver.*;

public class PrincessProverFactory implements ProverFactory {

	private final StringADTFactory stringADTFactory;
	private final FloatingPointADTFactory floatingPointADTFactory;

	public PrincessProverFactory() {
		this.stringADTFactory = new PrincessStringADTFactory();
		this.floatingPointADTFactory = new PrincessFloatingPointADTFactory();
	}

	public PrincessProverFactory(StringADTFactory stringADTFactory, FloatingPointADTFactory floatingPointADTFactory) {
		this.stringADTFactory = stringADTFactory;
		this.floatingPointADTFactory = floatingPointADTFactory;
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
}
