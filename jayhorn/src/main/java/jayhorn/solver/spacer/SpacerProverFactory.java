/**
 * 
 */
package jayhorn.solver.spacer;

import jayhorn.Log;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointType;

/**
 * @author schaef
 *
 */
public class SpacerProverFactory implements ProverFactory {

	private  SpacerProver spacer = null;

	private  SpacerFloatingPointADTFactory floatingPointADTFactory;
	private  SpacerTempFloatingPointADTFactory tempFloatingPointADTFactory;
	private  SpacerTempFloatingPointOperandsADTFactory tempFloatingPointOperandsADTFactory;



	/* (non-Javadoc)
	 * @see jhorn.solver.ProverFactory#spawn()
	 */
	@Override
	public Prover spawn() { // made spawn a singleton. TODO: check
		if (spacer != null) return spacer;
		SpacerProver spacer = null;
		try {
			spacer = new SpacerProver();
//			// initialization
			this.spacer = spacer;
			this.floatingPointADTFactory = new SpacerFloatingPointADTFactory(spacer.getCtx());
			this.tempFloatingPointADTFactory = new SpacerTempFloatingPointADTFactory(spacer.getCtx());
			this.tempFloatingPointOperandsADTFactory = new SpacerTempFloatingPointOperandsADTFactory(spacer.getCtx());

		} catch (UnsatisfiedLinkError e) {
			Log.error("Cannot start z3. "+e.toString());
		}
		return spacer;
	}

	/* (non-Javadoc)
	 * @see jhorn.solver.ProverFactory#spawnWithLog(java.lang.String)
	 */
	@Override
	public Prover spawnWithLog(String basename) {
		return spawn();
	}

	@Override
	public ProverADT spawnStringADT() {

		return new ProverADT() {
			@Override
			public ProverType getType(int typeIndex) {
				throw new RuntimeException("not implemented");
			}

			@Override
			public ProverExpr mkHavocExpr(int typeIndex) {
				throw new RuntimeException("not implemented");
			}

			@Override
			public ProverExpr mkCtorExpr(int ctorIndex, ProverExpr[] args) {
				throw new RuntimeException("not implemented");
			}

			@Override
			public ProverExpr mkSelExpr(int ctorIndex, int selIndex, ProverExpr term) {
				throw new RuntimeException("not implemented");
			}

			@Override
			public ProverExpr mkTestExpr(int ctorIndex, ProverExpr term) {
				throw new RuntimeException("not implemented");
			}

			@Override
			public ProverExpr mkSizeExpr(ProverExpr term) {
				throw new RuntimeException("not implemented");
			}
		};

	}

	@Override
	public ProverADT spawnFloatingPointADT(PrincessFloatingPointType.Precision precision) {
		return	this.floatingPointADTFactory.spawnFloatingPointADT(precision);
	}
	@Override
	public ProverADT spawnTempFloatingPointADT(PrincessFloatingPointType.Precision precision)
	{
		return 	this.tempFloatingPointADTFactory.spawnTempFloatingPointADT(precision);
	}
	@Override
	public ProverADT spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision precision, ProverADT tempFloatingPointADT)
	{
		return this.tempFloatingPointOperandsADTFactory.spawnTempFloatingPointOperandsADT(precision, tempFloatingPointADT);
	}

}
