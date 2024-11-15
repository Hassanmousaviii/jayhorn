package jayhorn.hornify;

import java.math.BigInteger;
import java.nio.charset.Charset;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import jayhorn.Log;
import jayhorn.hornify.encoder.MethodEncoder;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointType;
import soottocfg.cfg.Program;
import soottocfg.cfg.method.Method;

/**
 * Class to hornify Java program
 * 
 * @author teme
 *
 */

public class Hornify {

	private final ProverFactory factory;

	private Prover prover;

	public final List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();

	public Hornify(ProverFactory fac) {
		this.factory = fac;	
	}


    public HornEncoderContext toHorn(Program program){
        return toHorn(program, -1, HornEncoderContext.GeneratedAssertions.ALL);
    }

	/**
	 * Main method to encode into Horn
	 * @param program
	 */
	public HornEncoderContext toHorn(Program program,
                                     int explicitHeapSize,
                                     HornEncoderContext.GeneratedAssertions generatedAssertions){
		prover = factory.spawn();
		prover.setHornLogic(true);

		ProverADT floatingPointADT = factory.spawnFloatingPointADT(PrincessFloatingPointType.Precision.Single);
		ProverADT extendedFloatingPointADT = factory.spawnTempFloatingPointADT(PrincessFloatingPointType.Precision.Single);

		ProverADT doubleFloatingPointADT = factory.spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
		ProverADT extendedDoubleFloatingPointADT = factory.spawnTempFloatingPointADT(PrincessFloatingPointType.Precision.Double);
	/*	final ProverExpr s1 = prover.mkVariable("s1", prover.getBooleanType());
		final ProverExpr s2 = prover.mkVariable("s2", prover.getBooleanType());*/

		ProverFun xORSingleSigns = prover.mkDefinedFunction("xORSingleSigns",
				new ProverType[] {floatingPointADT.getType(0), floatingPointADT.getType(0) },
				prover.mkIte(
						prover.mkEq(
								floatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(0,floatingPointADT.getType(0))
								),
								floatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(1,floatingPointADT.getType(0))
								)
						),
						prover.mkLiteral(0),prover.mkLiteral(1)
				)
		);
		ProverFun requiredRoundingUp = prover.mkDefinedFunction("requiredRoundingUp" //LSB,G,R,S
				,new ProverType[] {prover.getBVType(1),prover.getBVType(1),prover.getBVType(1),prover.getBVType(1)},
				//prover.mkIte(
						prover.mkEq( //G.(LSB + (R+S)) = 1
								prover.mkBVAND(
										prover.mkBoundVariable(1, prover.getBVType(1)), //G
										prover.mkBVOR(
												prover.mkBoundVariable(0, prover.getBVType(1)), //LSB
												prover.mkBVOR(
														prover.mkBoundVariable(2, prover.getBVType(1)), //R
														prover.mkBoundVariable(3, prover.getBVType(1)), //S
														1
												),
												1
										),
										1
								),
								prover.mkBV(1,1)
						)/*,
						prover.mkLiteral(true),
						prover.mkLiteral(false)*/
				//)
		);

		//Functions for Single Precision

		ProverFun isOVFSingleExp = prover.mkDefinedFunction("isOVFSingleExp"
				,new ProverType[] {prover.getBVType(9)},

						prover.mkEq(
								prover.mkBVExtract(8,8,prover.mkBoundVariable(0, prover.getBVType(9))),
								prover.mkBV(1,1)
						)
		);
		ProverFun isUDFSingleExp = prover.mkDefinedFunction("isUDFSingleExp"
				,new ProverType[] {prover.getBVType(9)},
						prover.mkBVUlt(
								prover.mkBoundVariable(0, prover.getBVType(9)),
								prover.mkBV(1,9)
						)
		);

		ProverFun isOVFSingleSigInAdd = null;

		ProverFun isOVFSingleSigInMul = prover.mkDefinedFunction("isOVFSingleSigInMul"
				,new ProverType[] {prover.getBVType(48)},

						prover.mkEq(
								prover.mkBVExtract(47,47,prover.mkBoundVariable(0, prover.getBVType(48))),
								prover.mkBV(1,1)
						)
		);
		ProverFun extractSingleSigLSBInMul = prover.mkDefinedFunction("extractSingleSigLSBInMul"
				,new ProverType[] {prover.getBVType(48)},

								prover.mkBVExtract(23,23,prover.mkBoundVariable(0, prover.getBVType(48)))



		);
		ProverFun extractSingleSigGInMul = prover.mkDefinedFunction("extractSingleSigGInMul"
				,new ProverType[] {prover.getBVType(48)},

								prover.mkBVExtract(22,22,prover.mkBoundVariable(0, prover.getBVType(48)))

		);
		ProverFun extractSingleSigRInMul = prover.mkDefinedFunction("extractSingleSigRInMul"
				,new ProverType[] {prover.getBVType(48)},

								prover.mkBVExtract(21,21,prover.mkBoundVariable(0, prover.getBVType(48)))


		);
		ProverFun computeSingleSigStickyInMul = prover.mkDefinedFunction("computeSingleSigStickyInMul"
				,new ProverType[] {prover.getBVType(48)},
				prover.mkIte(
						prover.mkEq(
								prover.mkBVExtract(20,0,prover.mkBoundVariable(0, prover.getBVType(48))),
								prover.mkBV(0,21)
						),
						prover.mkBV(0,1),
						prover.mkBV(1,1)
				)
		);
		ProverFun roundUpSingleSigInMul = prover.mkDefinedFunction("roundUpSingleSigInMul"
				,new ProverType[] {floatingPointADT.getType(0)},
				extendedFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						floatingPointADT.mkSelExpr(
								0,
								0,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //Sign
						prover.mkBVZeroExtend(
								1,
								floatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(0,floatingPointADT.getType(0))
								),
								8
						), //exponent
						prover.mkBVPlus(
								prover.mkBVConcat(
										prover.mkBVZeroExtend(1,
										floatingPointADT.mkSelExpr(
												0,
												2,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										),24),
										prover.mkBV(0,23),
										48
								),
								prover.mkBV(new BigInteger("8388608"),48),
								48
						), //mantissa
						floatingPointADT.mkSelExpr(0,3,prover.mkBoundVariable(0,floatingPointADT.getType(0))),//isInf
						floatingPointADT.mkSelExpr(0,4,prover.mkBoundVariable(0,floatingPointADT.getType(0))),//isNaN
						floatingPointADT.mkSelExpr(0,5,prover.mkBoundVariable(0,floatingPointADT.getType(0))),//OVF
						floatingPointADT.mkSelExpr(0,6,prover.mkBoundVariable(0,floatingPointADT.getType(0))) //UDF
				}));
		ProverFun makeSingleOVFFun = prover.mkDefinedFunction("makeSingleOVFFun" //sign
				,new ProverType[] {prover.getBooleanType()},
				floatingPointADT.mkCtorExpr(0,
						new ProverExpr[]{
								prover.mkBoundVariable(0,prover.getBooleanType()),
								prover.mkBV(255,8),
								prover.mkBV(0,24),
								prover.mkLiteral(1), //Inf
								prover.mkLiteral(0), //NaN
								prover.mkLiteral(1), //OVF
								prover.mkLiteral(0) //UDF
						}
				)
		);
		ProverFun makeSingleUDFFun = prover.mkDefinedFunction("makeSingleUDFFun" //sign
				,new ProverType[] {prover.getBooleanType()},
				floatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkBoundVariable(0,prover.getBooleanType()),
						prover.mkBV(0,8),
						prover.mkBV(0,24),
						prover.mkLiteral(0), //Inf
						prover.mkLiteral(0), //NaN
						prover.mkLiteral(0), //OVF
						prover.mkLiteral(1) //UDF
				}));
		ProverFun makeSingleNaNFun = prover.mkDefinedFunction("makeSingleNaNFun"
				,new ProverType[] {floatingPointADT.getType(0)},
				floatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkLiteral(0),
						prover.mkBV(0,8),
						prover.mkBV(0,24),
						prover.mkLiteral(0), //Inf
						prover.mkLiteral(1), //NaN
						prover.mkLiteral(0), //OVF
						prover.mkLiteral(0) //UDF
				}));
		ProverFun makeSingleInfFun = prover.mkDefinedFunction("makeSingleInfFun"
				,new ProverType[] {floatingPointADT.getType(0)},
				floatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						floatingPointADT.mkSelExpr(
								0,
								0,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //Sign
						floatingPointADT.mkSelExpr(
								0,
								1,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //exponent
						floatingPointADT.mkSelExpr(
								0,
								2,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //mantissa
						prover.mkLiteral(1), //Inf
						floatingPointADT.mkSelExpr(
								0,
								4,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //NaN
						floatingPointADT.mkSelExpr(
								0,
								5,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //OVF
						floatingPointADT.mkSelExpr(
								0,
								6,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						) //UDF
				}));
		ProverFun negateSingleFun = prover.mkDefinedFunction("negateSingleFun"
				,new ProverType[] {floatingPointADT.getType(0)},
				floatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkIte(
								prover.mkEq(
										floatingPointADT.mkSelExpr(
												0,
												0,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										),
										prover.mkLiteral(1)
								),
								prover.mkLiteral(0),
								prover.mkLiteral(1)
						),//Sign
						floatingPointADT.mkSelExpr(
								0,
								1,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //exponent
						floatingPointADT.mkSelExpr(
								0,
								2,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //mantissa
						floatingPointADT.mkSelExpr(
								0,
								3,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //Inf
						floatingPointADT.mkSelExpr(
								0,
								4,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //NaN
						floatingPointADT.mkSelExpr(
								0,
								5,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						), //OVF
						floatingPointADT.mkSelExpr(
								0,
								6,
								prover.mkBoundVariable(0,floatingPointADT.getType(0))
						) //UDF
				}));
		ProverFun isSingleNaN = prover.mkDefinedFunction("isSingleNaN" //FP
				,new ProverType[] {floatingPointADT.getType(0)},

						prover.mkOr(
								prover.mkEq( //isNaN = true
										floatingPointADT.mkSelExpr(
												0,
												4,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										), //isNaN
										prover.mkLiteral(1)
								),
								prover.mkAnd(  //e=11...1 and m != 0
										prover.mkEq(
												floatingPointADT.mkSelExpr(
														0,
														1,
														prover.mkBoundVariable(0,floatingPointADT.getType(0))
												), //e
												prover.mkBV(255,8)
										),
										prover.mkNot(
												prover.mkEq(
														floatingPointADT.mkSelExpr(
																0,
																2,
																prover.mkBoundVariable(0,floatingPointADT.getType(0))
														),
														prover.mkBV(0,24)
												)
										)
								)
						)
		);
		ProverFun isSingleInf = prover.mkDefinedFunction("isSingleInf" //FP
				,new ProverType[] {floatingPointADT.getType(0)},

						prover.mkOr(
								prover.mkEq( //IsInf = true
										floatingPointADT.mkSelExpr(
												0,
												3,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										),
										prover.mkLiteral(1)
								),
								prover.mkAnd( //e=11...1 and m = 0
										prover.mkEq(
												floatingPointADT.mkSelExpr(
														0,
														1,
														prover.mkBoundVariable(0,floatingPointADT.getType(0))
												),
												prover.mkBV(255,8)
										),
										prover.mkEq(
												floatingPointADT.mkSelExpr(
														0,
														2,
														prover.mkBoundVariable(0,floatingPointADT.getType(0))
												),
												prover.mkBV(0,24)
										)

								)
						));
		ProverFun isSingleZero = prover.mkDefinedFunction("isSingleZero" //FP
				,new ProverType[] {floatingPointADT.getType(0)},

						prover.mkAnd(
								prover.mkEq(
										floatingPointADT.mkSelExpr(
												0,
												1,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										),
										prover.mkBV(0,8)
								),
								prover.mkEq(
										floatingPointADT.mkSelExpr(
												0,
												2,
												prover.mkBoundVariable(0,floatingPointADT.getType(0))
										),
										prover.mkBV(0,24)
								)

						));
		ProverFun areEqSingleSigns = prover.mkDefinedFunction("areEqSingleSigns" //FP
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},

						prover.mkEq(
								floatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(0,floatingPointADT.getType(0))
								),
								floatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(1,floatingPointADT.getType(0))
								)
						));
		ProverFun isSingleNeg = prover.mkDefinedFunction("isSingleNeg" //FP
				,new ProverType[] {floatingPointADT.getType(0)},

						prover.mkEq( //sign = 1
								floatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(0,floatingPointADT.getType(0))
								),
								prover.mkLiteral(1)
						));
		ProverFun existSingleNaN = prover.mkDefinedFunction("existSingleNaN"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},

						prover.mkOr(
								isSingleNaN.mkExpr(prover.mkBoundVariable(0,floatingPointADT.getType(0))),
								isSingleNaN.mkExpr(prover.mkBoundVariable(1,floatingPointADT.getType(0)))
						));
		ProverFun existSingleInf = prover.mkDefinedFunction("existSingleInf"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},

						prover.mkOr(
								isSingleInf.mkExpr(prover.mkBoundVariable(0,floatingPointADT.getType(0))),
								isSingleInf.mkExpr(prover.mkBoundVariable(1,floatingPointADT.getType(0)))
						));
		ProverFun singleOperandsEqZero = prover.mkDefinedFunction("singleOperandsEqZero"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},
						prover.mkAnd(
								isSingleZero.mkExpr(prover.mkBoundVariable(0,floatingPointADT.getType(0))),
								isSingleZero.mkExpr(prover.mkBoundVariable(1,floatingPointADT.getType(0)))
						));
		ProverFun singleOperandsEqInf = prover.mkDefinedFunction("singleOperandsEqInf"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},

						prover.mkAnd(
								isSingleInf.mkExpr(prover.mkBoundVariable(0,floatingPointADT.getType(0))),
								isSingleInf.mkExpr(prover.mkBoundVariable(1,floatingPointADT.getType(0)))
						));
		ProverFun existSingleZero = prover.mkDefinedFunction("existSingleZero"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								isSingleZero.mkExpr(prover.mkBoundVariable(0,floatingPointADT.getType(0))),
								isSingleZero.mkExpr(prover.mkBoundVariable(1,floatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun existSpecCasForSingleInMul = prover.mkDefinedFunction("existSpecCasForSingleInMul"
				,new ProverType[] {floatingPointADT.getType(0),floatingPointADT.getType(0)},

						prover.mkOr(
								existSingleNaN.mkExpr(
										prover.mkBoundVariable(0,floatingPointADT.getType(0)),
										prover.mkBoundVariable(1,floatingPointADT.getType(0))
								),
								existSingleInf.mkExpr(
										prover.mkBoundVariable(0,floatingPointADT.getType(0)),
										prover.mkBoundVariable(1,floatingPointADT.getType(0))
								)
						));

		//Functions for Double Precision
		ProverFun xORDoubleSigns = prover.mkDefinedFunction("xORDoubleSigns",
				new ProverType[] {doubleFloatingPointADT.getType(0), doubleFloatingPointADT.getType(0) },
				prover.mkIte(
						prover.mkEq(
								doubleFloatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
								),
								doubleFloatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0))
								)
						),
						prover.mkLiteral(0),prover.mkLiteral(1)
				)
		);
		ProverFun isOVFDoubleExp = prover.mkDefinedFunction("isOVFDoubleExp"
				,new ProverType[] {prover.getBVType(12)},
				//prover.mkIte(
						prover.mkEq(prover.mkBVExtract(11,11,prover.mkBoundVariable(0, prover.getBVType(12))),
								prover.mkBV(1,1)
						)/*,
						prover.mkLiteral(true),
						prover.mkLiteral(false)
				)*/
		);
		ProverFun isUDFDoubleExp = prover.mkDefinedFunction("isUDFDoubleExp"
				,new ProverType[] {prover.getBVType(12)},
				//prover.mkIte(
						prover.mkBVUlt(prover.mkBoundVariable(0, prover.getBVType(12)),
								prover.mkBV(1,12)
						)/*,
						prover.mkLiteral(true),
						prover.mkLiteral(false)*/
				//)
		);
		ProverFun isOVFDoubleSigInAdd = null;
		ProverFun isOVFDoubleSigInMul = prover.mkDefinedFunction("isOVFDoubleSigInMul"
				,new ProverType[] {prover.getBVType(106)},
				//prover.mkIte(
						prover.mkEq(
								prover.mkBVExtract(105,105,prover.mkBoundVariable(0, prover.getBVType(106))),
								prover.mkBV(1,1)
						)/*,
						prover.mkLiteral(true),
						prover.mkLiteral(false)*/
				//)
		);

		ProverFun extractDoubleSigLSBInMul = prover.mkDefinedFunction("extractDoubleSigLSBInMul"
				,new ProverType[] {prover.getBVType(106)},
				prover.mkBVExtract(52,52,prover.mkBoundVariable(0, prover.getBVType(106))));

		ProverFun extractDoubleSigGInMul = prover.mkDefinedFunction("extractDoubleSigGInMul"
				,new ProverType[] {prover.getBVType(106)},

								prover.mkBVExtract(51,51,prover.mkBoundVariable(0, prover.getBVType(106)))


		);
		ProverFun extractDoubleSigRInMul = prover.mkDefinedFunction("extractDoubleSigRInMul"
				,new ProverType[] {prover.getBVType(106)},

								prover.mkBVExtract(50,50,prover.mkBoundVariable(0, prover.getBVType(106)))

		);
		ProverFun computeDoubleSigStickyInMul = prover.mkDefinedFunction("computeDoubleSigStickyInMul"
				,new ProverType[] {prover.getBVType(106)},
				prover.mkIte(
						prover.mkEq(
								prover.mkBVExtract(49,0,prover.mkBoundVariable(0, prover.getBVType(106))),
								prover.mkBV(0,50)
						),
						prover.mkBV(0,1),
						prover.mkBV(1,1)
				)
		);

		ProverFun roundUpDoubleSigInMul = prover.mkDefinedFunction("roundUpDoubleSigInMul"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				extendedDoubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						doubleFloatingPointADT.mkSelExpr(
								0,
								0,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //Sign
						prover.mkBVZeroExtend(
								1,
								doubleFloatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
								),
								11
						), //exponent
						prover.mkBVPlus(
								prover.mkBVConcat(
										prover.mkBVZeroExtend(1,
										doubleFloatingPointADT.mkSelExpr(
												0,
												2,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										), 53),
										prover.mkBV(0,52),
										106
								),
								//
//4503599627370496
								prover.mkBV(new BigInteger("4503599627370496"),106),
								106
						), //mantissa
						doubleFloatingPointADT.mkSelExpr(0,3,prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),//isInf
						doubleFloatingPointADT.mkSelExpr(0,4,prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),//isNaN
						doubleFloatingPointADT.mkSelExpr(0,5,prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),//OVF
						doubleFloatingPointADT.mkSelExpr(0,6,prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0)))//UDF
				}));

		ProverFun makeDoubleOVFFun = prover.mkDefinedFunction("makeDoubleOVFFun" //sign
				,new ProverType[] {prover.getBooleanType()},
				doubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkBoundVariable(0,prover.getBooleanType()),
						prover.mkBV(2047,11),
						prover.mkBV(0,53),
						prover.mkLiteral(true), //Inf
						prover.mkLiteral(false), //NaN
						prover.mkLiteral(true), //OVF
						prover.mkLiteral(false) //UDF
				}));

		ProverFun makeDoubleUDFFun = prover.mkDefinedFunction("makeDoubleUDFFun" //sign
				,new ProverType[] {prover.getBooleanType()},
				doubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkBoundVariable(0,prover.getBooleanType()),
						prover.mkBV(0,11),
						prover.mkBV(0,53),
						prover.mkLiteral(false), //Inf
						prover.mkLiteral(false), //NaN
						prover.mkLiteral(false), //OVF
						prover.mkLiteral(true) //UDF
				}));
		ProverFun makeDoubleNaNFun = prover.mkDefinedFunction("makeDoubleNaNFun"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				doubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkLiteral(false),
						prover.mkBV(0,11),
						prover.mkBV(0,53),
						prover.mkLiteral(false), //Inf
						prover.mkLiteral(true), //NaN
						prover.mkLiteral(false), //OVF
						prover.mkLiteral(false) //UDF
				}));
		ProverFun makeDoubleInfFun = prover.mkDefinedFunction("makeDoubleInfFun"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				doubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						doubleFloatingPointADT.mkSelExpr(
								0,
								0,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //Sign
						doubleFloatingPointADT.mkSelExpr(
								0,
								1,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //exponent
						doubleFloatingPointADT.mkSelExpr(
								0,
								2,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //mantissa
						prover.mkLiteral(true), //Inf
						doubleFloatingPointADT.mkSelExpr(
								0,
								4,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //NaN
						doubleFloatingPointADT.mkSelExpr(
								0,
								5,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //OVF
						doubleFloatingPointADT.mkSelExpr(
								0,
								6,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						) //UDF
				}));

		ProverFun negateDoubleFun = prover.mkDefinedFunction("negateDoubleFun"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				doubleFloatingPointADT.mkCtorExpr(0,new ProverExpr[]{
						prover.mkIte(
								prover.mkEq(
										doubleFloatingPointADT.mkSelExpr(
												0,
												0,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										),
										prover.mkLiteral(true)
								),
								prover.mkLiteral(false),
								prover.mkLiteral(true)
						),//Sign
						doubleFloatingPointADT.mkSelExpr(
								0,
								1,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //exponent
						doubleFloatingPointADT.mkSelExpr(
								0,
								2,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //mantissa
						doubleFloatingPointADT.mkSelExpr(
								0,
								3,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //Inf
						doubleFloatingPointADT.mkSelExpr(
								0,
								4,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //NaN
						doubleFloatingPointADT.mkSelExpr(
								0,
								5,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						), //OVF
						doubleFloatingPointADT.mkSelExpr(
								0,
								6,
								prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
						) //UDF
				}));

		ProverFun areEqDoubleSigns = prover.mkDefinedFunction("areEqDoubleSigns" //doubleFP
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkEq(
								doubleFloatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(0,floatingPointADT.getType(0))
								),
								doubleFloatingPointADT.mkSelExpr(
										0,
										1,
										prover.mkBoundVariable(1,floatingPointADT.getType(0))
								)
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));

		ProverFun isDoubleNeg = prover.mkDefinedFunction("isDoubleNeg" //doubleFP
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkEq( //sign = 1
								doubleFloatingPointADT.mkSelExpr(
										0,
										0,
										prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
								),
								prover.mkLiteral(1)
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun isDoubleZero = prover.mkDefinedFunction("isDoubleZero"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkAnd(
								prover.mkEq(
										doubleFloatingPointADT.mkSelExpr(
												0,
												1,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										),
										prover.mkBV(0,11)
								),
								prover.mkEq(
										doubleFloatingPointADT.mkSelExpr(
												0,
												2,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										),
										prover.mkBV(0,53)
								)

						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun isDoubleNaN = prover.mkDefinedFunction("isDoubleNaN"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								prover.mkEq(
										doubleFloatingPointADT.mkSelExpr(
												0,
												4,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										),
										prover.mkLiteral(true)
								), //isNaN = true
								prover.mkAnd( //e=11...1 and m != 0
										prover.mkEq(
												doubleFloatingPointADT.mkSelExpr(
														0,
														1,
														prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
												),
												prover.mkBV(2047,11)
										),
										prover.mkNot(
												prover.mkEq(
														doubleFloatingPointADT.mkSelExpr(
																0,
																2,
																prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
														),
														prover.mkBV(0,53))
										)
								)
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun existDoubleNaN = prover.mkDefinedFunction("existDoubleNaN"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								isDoubleNaN.mkExpr(prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),
								isDoubleNaN.mkExpr(prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun isDoubleInf = prover.mkDefinedFunction("isDoubleInf"
				,new ProverType[] {doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								prover.mkEq(
										doubleFloatingPointADT.mkSelExpr(
												0,
												3,
												prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
										),
										prover.mkLiteral(true)
								), //IsInf = true
								prover.mkAnd( //e=11...1 and m = 0
										prover.mkEq(
												doubleFloatingPointADT.mkSelExpr(
														0,
														1,
														prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
												),
												prover.mkBV(2047,8)
										),
										prover.mkEq(
												doubleFloatingPointADT.mkSelExpr(
														0,
														2,
														prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))
												),
												prover.mkBV(0,53)
										)

								)
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));

		ProverFun existDoubleInf = prover.mkDefinedFunction("existDoubleInf"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								isDoubleInf.mkExpr(prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),
								isDoubleInf.mkExpr(prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun doubleOperandsEqZero = prover.mkDefinedFunction("doubleOperandsEqZero"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkAnd(
								isDoubleZero.mkExpr(prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),
								isDoubleZero.mkExpr(prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun doubleOperandsEqInf = prover.mkDefinedFunction("doubleOperandsEqInf"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkAnd(
								isDoubleInf.mkExpr(prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),
								isDoubleInf.mkExpr(prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));

		ProverFun existDoubleZero = prover.mkDefinedFunction("existDoubleZero"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								isDoubleZero.mkExpr(prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0))),
								isDoubleZero.mkExpr(prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0)))
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));
		ProverFun existSpecCasForDoubleInMul = prover.mkDefinedFunction("existSpecCasForDoubleInMul"
				,new ProverType[] {doubleFloatingPointADT.getType(0),doubleFloatingPointADT.getType(0)},
				prover.mkIte(
						prover.mkOr(
								existDoubleNaN.mkExpr(
										prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0)),
										prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0))
								),
								existDoubleInf.mkExpr(
										prover.mkBoundVariable(0,doubleFloatingPointADT.getType(0)),
										prover.mkBoundVariable(1,doubleFloatingPointADT.getType(0))
								)
						),
						prover.mkLiteral(true), prover.mkLiteral(false)
				));

		HornEncoderContext hornContext = new HornEncoderContext(
				prover,
				program,
				factory.spawnStringADT(),

				factory.spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision.Single,extendedFloatingPointADT),
				factory.spawnTempFloatingPointOperandsADT(PrincessFloatingPointType.Precision.Double,extendedDoubleFloatingPointADT),
				requiredRoundingUp,

				floatingPointADT,
				extendedFloatingPointADT,
				xORSingleSigns,
				isOVFSingleExp,
				isUDFSingleExp,
				isOVFSingleSigInAdd,
				isOVFSingleSigInMul,
				extractSingleSigLSBInMul,
				extractSingleSigGInMul,
				extractSingleSigRInMul,
				computeSingleSigStickyInMul,
				roundUpSingleSigInMul,
				makeSingleOVFFun,
				makeSingleUDFFun,
				existSingleZero,
				existSingleInf,
				existSingleNaN,
				singleOperandsEqInf,
				singleOperandsEqZero,
				isSingleNeg,
				areEqSingleSigns,
				isSingleInf,
				isSingleNaN,
				makeSingleNaNFun,
				negateSingleFun,
				makeSingleInfFun,
				existSpecCasForSingleInMul,

				doubleFloatingPointADT,
				extendedDoubleFloatingPointADT,
				xORDoubleSigns,
				isOVFDoubleExp,
				isUDFDoubleExp,
				isOVFDoubleSigInAdd,
				isOVFDoubleSigInMul,
				extractDoubleSigLSBInMul,
				extractDoubleSigGInMul,
				extractDoubleSigRInMul,
				computeDoubleSigStickyInMul,
				roundUpDoubleSigInMul,
				makeDoubleOVFFun,
				makeDoubleUDFFun,
				existDoubleZero,
				existDoubleInf,
				existDoubleNaN,
				doubleOperandsEqInf,
				doubleOperandsEqZero,
				isDoubleNeg,
				areEqDoubleSigns,
				isDoubleInf,
				isDoubleNaN,
				makeDoubleNaNFun,
				negateDoubleFun,
				makeDoubleInfFun,
				existSpecCasForDoubleInMul,

				explicitHeapSize, generatedAssertions);

		Log.info("Transform Program Methods into Horn Clauses ... ");

		for (Method method : program.getMethods()) {
			final MethodEncoder encoder = new MethodEncoder(prover, method, hornContext);
			clauses.addAll(encoder.encode());		
		}
		
		return hornContext;
	}

	/**
	 * Return the current prover object
	 * @return prover
	 */
	public Prover getProver() {
		return prover;
	}


	/**
	 * Write clauses
	 * @return
	 */
	public String writeHorn() {
		StringBuilder st = new StringBuilder();
		for (ProverHornClause clause : clauses)
			st.append("\t\t" + clause + "\n");
		st.append("\t\t-------------\n");
		return st.toString();
	}

	/**
	 * Write Horn clauses to file
	 */
	public static void hornToFile(List<ProverHornClause> clauses,
			int num) {
		// write Horn clauses to file
		String out = jayhorn.Options.v().getOutDir();
		if (out != null) {
			String basename = jayhorn.Options.v().getOutBasename();
			Path file = Paths.get(out + basename + "_" + num + ".horn");

			LinkedList<String> it = new LinkedList<String>();
			for (ProverHornClause clause : clauses)
				it.add("\t\t" + clause);

			writeToFile(file, it);
		}
	}

	/**
	 * Write Horn clauses to an SMT-LIB file
	 */
	public static void hornToSMTLIBFile(List<ProverHornClause> clauses,
			int num,
			Prover prover) {
		String out = jayhorn.Options.v().getOutDir();
		if (out != null) {
			String basename = jayhorn.Options.v().getOutBasename();
			Path file = Paths.get(out + basename + "_" + num + ".smt2");

			Log.info("Writing Horn clauses to " + file);

			LinkedList<String> it = new LinkedList<String>();

                        it.add(prover.toSMTLIBScript(clauses));
			writeToFile(file, it);
		}
	}

	private static void writeToFile(Path file, List<String> it) {
		try {					
			Path parent = file.getParent();
			if (parent != null)
				Files.createDirectories(parent);
			Files.write(file, it, Charset.forName("UTF-8"));
		} catch (Exception e) {
			System.err.println("Error writing file " + file);
		}
	}


}
