/**
 * 
 */
package jayhorn.hornify.encoder;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;

import com.google.common.base.Verify;

import jayhorn.hornify.HornEncoderContext;
import jayhorn.hornify.HornHelper;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessADTType;
import jayhorn.solver.princess.PrincessFloatingPointADTFactory;
import jayhorn.solver.princess.PrincessFloatingPointType;
import jayhorn.solver.princess.PrincessStringADTFactory;
import soottocfg.cfg.Program;
import soottocfg.cfg.expression.BinaryExpression;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.expression.IteExpression;
import soottocfg.cfg.expression.TupleAccessExpression;
import soottocfg.cfg.expression.UnaryExpression;
import soottocfg.cfg.expression.literal.*;
import soottocfg.cfg.type.ReferenceType;
import soottocfg.cfg.variable.ClassVariable;
import soottocfg.cfg.variable.Variable;

/**
 * @author schaef
 *
 */
public class ExpressionEncoder {

	private final Prover p;
	private final HornEncoderContext hornContext;

	private final StringEncoder stringEncoder;

	private final FloatingPointEncoder singleFloatingPointEnCoder;

	private final FloatingPointEncoder doubleFloatingPointEnCoder;

	//private final F

	/**
	 * 
	 */
	public ExpressionEncoder(Prover p, HornEncoderContext hornContext) {
		this.p = p;
		this.hornContext = hornContext;
		this.stringEncoder = new StringEncoder(p, HornHelper.hh().getStringADT());
		this.singleFloatingPointEnCoder = new FloatingPointEncoder(p,HornHelper.hh().getSingleFloatingPointADT(), FloatingPointEncoder.Precision.Single);
		this.doubleFloatingPointEnCoder = new FloatingPointEncoder(p,HornHelper.hh().getDoubleFloatingPointADT(), FloatingPointEncoder.Precision.Double);

	}

	public StringEncoder getStringEncoder() {
		return stringEncoder;
	}

	public FloatingPointEncoder getSingleFloatingPointEnCoder(){return singleFloatingPointEnCoder;}

	public FloatingPointEncoder getDoubleFloatingPointEnCoder(){return doubleFloatingPointEnCoder;}

	public HornEncoderContext getContext() {
		return this.hornContext;
	}

        public static class OverApproxException extends RuntimeException {}

	/**
	 * TODO: this is a hack!
	 * 
	 * @param id
	 * @return
	 */
	private ProverExpr typeIdToProverExpr(int id) {
		return p.mkLiteral(id);
	}
	
        private ProverExpr varToProverExpr(Variable var, Map<Variable, ProverExpr> varMap) {
            if (var instanceof ClassVariable) {
                return typeIdToProverExpr(hornContext.getTypeID((ClassVariable) var));
            } else {
                if (hornContext.elimOverApprox() && Program.isAbstractedVariable(var))
                    throw new OverApproxException();
                final ProverExpr proverVar = HornHelper.hh().findOrCreateProverVar(p, var, varMap);
                if (hornContext.getProgram().getGlobalVariables().contains(var)) {
                    /*
                     * For globals, we just use an integer number.
                     * NOTE: The translation guarantees that this number is unique and different
                     * from Null.
                     */
                    int idx = hornContext.getProgram().getGlobalVariables().indexOf(var);
                    return makeUniqueReference(p, var, proverVar, -idx - 1);
                }
                
                return proverVar;
            }
        }

	public List<ProverHornClause> getExtraEncodedClauses() {
		return stringEncoder.getEncodedClauses();
	}

	public ProverExpr exprToProverExpr(Expression e, Map<Variable, ProverExpr> varMap) {
		if (e instanceof StringLiteral) {	// check before (e instanceof IdentifierExpression)
//			return stringEncoder.mkString(((StringLiteral) e).getValue());
			StringLiteral stl = (StringLiteral) e;
			ProverExpr str = stringEncoder.mkStringPE(stl.getValue());
			ProverExpr ref = varToProverExpr(stl.getVariable(), varMap);
//			stringEncoder.assertStringLiteral(ref, ste, (ReferenceType)e.getType());
//			return ref;
			return p.mkTupleUpdate(ref, 3, str);

		} else if (e instanceof DoubleLiteral) {
			DoubleLiteral doubleLiteral = (DoubleLiteral) e;
			ProverExpr dble = doubleFloatingPointEnCoder.mkDoublePE(doubleLiteral.getValue());
			ProverExpr ref = varToProverExpr(doubleLiteral.getVariable(),varMap);

			return p.mkTupleUpdate(ref,3, dble);
			/*DoubleLiteral doubleLiteral = (DoubleLiteral) e;
			return doubleFloatingPointEnCoder.mkDoublePE(doubleLiteral.getValue());*/

		} else if (e instanceof IdentifierExpression) {
			Variable var = ((IdentifierExpression) e).getVariable();
                        return varToProverExpr(var, varMap);
		} else if (e instanceof TupleAccessExpression) {
			TupleAccessExpression tae = (TupleAccessExpression) e;
			ProverExpr tuple = varToProverExpr(tae.getVariable(), varMap);
			return p.mkTupleSelect(tuple, tae.getAccessPosition());
			// return p.mkVariable("HACK_FreeVar" + HornHelper.hh().newVarNum(),
			// HornHelper.hh().getProverType(p, tae.getType()));
		} else if (e instanceof IntegerLiteral) {
			return p.mkLiteral(BigInteger.valueOf(((IntegerLiteral) e).getValue()));
		} else if (e instanceof NullLiteral) {
			return p.mkLiteral(HornHelper.NullValue);
		} else if (e instanceof BinaryExpression) {
			final BinaryExpression be = (BinaryExpression) e;
			ProverExpr left = exprToProverExpr(be.getLeft(), varMap);

			ProverExpr right = exprToProverExpr(be.getRight(), varMap);


			// if (right instanceof ProverTupleType) {
			// //in that case only use the projection to the first element
			// //of the tuple.
			// Verify.verify(right instanceof ProverTupleExpr, be.getRight()+"
			// becomes " +right +" of type " + right.getType().getClass());
			// right = p.mkTupleSelect(right, 0);
			// }

			if (be.getLeft() instanceof NullLiteral && be.getRight() instanceof IdentifierExpression) {
				right = p.mkTupleSelect(right, 0);
			}
			if (be.getRight() instanceof NullLiteral && be.getLeft() instanceof IdentifierExpression) {
				left = p.mkTupleSelect(left, 0);
			}

			// TODO: the following choices encode Java semantics
			// of various operators; need a good schema to choose
			// how precise the encoding should be (probably
			// configurable)
			switch (be.getOp()) {
			case Plus:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr) left;
					ProverTupleExpr tRight = (ProverTupleExpr) right;
					//((PrincessADTType) tLeft.getSubExpr(3))

					if (tLeft.getArity() == 4)
						if (((PrincessADTType) tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));

							return p.mkTuple(new ProverExpr[]{tLeft.getSubExpr(0),tLeft.getSubExpr(1), tLeft.getSubExpr(2),
									p.mkIte(
									p.mkEq(leftSign,rightSign), //left.s == right.s
									p.mkIte(p.mkEq(leftExponent,rightExponent),  //left.e == right.e

											doubleFloatingPointEnCoder.mkDoublePE(leftSign, //sign
													p.mkIte( // exponent
															p.mkEq(p.mkBVExtract(53,53,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(1,rightMantisa,53),54)),p.mkBV(1,1)), // Overflow?
															p.mkBVPlus(leftExponent,p.mkBV(1,11),11), //overflow occured! => e= e+1
															leftExponent // No overflow! => e = e
															),
													p.mkIte( // Mantissa
															p.mkEq(p.mkBVExtract(1,1,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(1,rightMantisa,53),54)),p.mkBV(1,1)),
															p.mkBVPlus(p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(1,rightMantisa,53),54)),p.mkBV(1,53),53),
															p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(1,rightMantisa,53),54))
													)
													),
											p.mkIte(p.mkBVUge(leftExponent,rightExponent),

													doubleFloatingPointEnCoder.mkDoublePE(leftSign, //sign
															p.mkBVPlus(leftExponent,p.mkBV(1,11),11), // exponent
															p.mkIte(
																	p.mkEq(p.mkBVExtract(0,0,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(leftExponent,rightExponent,11),53),54),54)),p.mkBV(1,1)),
																	p.mkBVPlus(p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(leftExponent,rightExponent,11),53),54),54)),p.mkBV(1,53),53),
																	p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(leftExponent,rightExponent,11),53),54),54))
															)
													),

													doubleFloatingPointEnCoder.mkDoublePE(leftSign, //sign
															p.mkBVPlus(rightExponent,p.mkBV(1,11),11), // exponent
															p.mkIte(
																	p.mkEq(p.mkBVExtract(0,0,p.mkBVPlus(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(rightExponent,leftExponent,11),53),54),54)),p.mkBV(1,1)),
																	p.mkBVPlus(p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(rightExponent,leftExponent,11),53),54),54)),p.mkBV(1,53),53),
																	p.mkBVExtract(53,1,p.mkBVPlus(p.mkBVZeroExtend(1,rightMantisa,53),p.mkBVlshr(p.mkBVZeroExtend(1,leftMantisa,53),p.mkBVZeroExtend(43,p.mkBVSub(rightExponent,leftExponent,11),54),53),54))
															)
													)
													)

											),
									doubleFloatingPointEnCoder.mkDoublePE(p.mkBV(0,1),p.mkBV(1021,11),p.mkBV(new BigInteger("5404319552844596"),53))//ToDo: oposite sign in addition
									)});
							//ProverExpr [] subExprs = {tLeft.getSubExpr(0),tLeft.getSubExpr(1), tLeft.getSubExpr(2),BVaddExpr};
							//return p.mkTuple(subExprs);
						}
				}
				return p.mkPlus(left, right);
			case Minus:
				return p.mkMinus(left, right);
			case Mul:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;

					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));

							return p.mkTuple(new ProverExpr[]{tLeft.getSubExpr(0), tLeft.getSubExpr(1), tLeft.getSubExpr(2),
									p.mkIte(p.mkEq(
													p.mkBVExtract(105, 105,
															p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																	  p.mkBVZeroExtend(53, rightMantisa, 53),
																	106
															)
													),
													p.mkBV(1, 1)
											),
											doubleFloatingPointEnCoder.mkDoublePE(
													p.mkBVXOR(leftSign, rightSign, 1), //sign
													p.mkBVPlus(
															   p.mkBVSub(p.mkBVPlus(leftExponent, rightExponent, 11),
																	   p.mkBV(1023, 11), 11),
															   p.mkBV(1, 11),
															11
													), // exponent
													p.mkIte( //Mantissa
															p.mkEq(
																	p.mkBVExtract(52, 52,
																			p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																					p.mkBVZeroExtend(53, rightMantisa, 53), 106)),
																	p.mkBV(1, 1)),
															p.mkBVPlus(p.mkBVExtract(105, 53,
																			p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																					p.mkBVZeroExtend(53, rightMantisa, 53), 106)),
																	p.mkBV(1, 53), 53),
															p.mkBVExtract(105, 53,
																	p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																			p.mkBVZeroExtend(53, rightMantisa, 53), 106))
													)
											),
											doubleFloatingPointEnCoder.mkDoublePE(p.mkBVXOR(leftSign, rightSign, 1), //sign
													p.mkBVSub(
															 p.mkBVPlus(leftExponent, rightExponent, 11),
															 p.mkBV(1023, 11),
															11
													), // exponent
													p.mkIte(
															p.mkEq(
																	p.mkBVExtract(51, 51,
																			p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																					p.mkBVZeroExtend(53, rightMantisa, 53), 106)),
																	p.mkBV(1, 1)),
															p.mkBVPlus(p.mkBVExtract(104, 52,
																			p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																					p.mkBVZeroExtend(53, rightMantisa, 53), 106)),
																	p.mkBV(1, 53), 53),
															p.mkBVExtract(104, 52,
																	p.mkBVMul(p.mkBVZeroExtend(53, leftMantisa, 53),
																			p.mkBVZeroExtend(53, rightMantisa, 53), 106))
													)
											)
									)
							});


						}
				}
				return p.mkMult(left, right);
			case Div:
				return p.mkTDiv(left, right);
			case Mod:
				return p.mkTMod(left, right);
			case Eq:
		        if (left instanceof ProverTupleExpr) {
		            ProverTupleExpr tLeft = (ProverTupleExpr)left;
		            ProverTupleExpr tRight = (ProverTupleExpr)right;

					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint"))
							return p.mkEq(tLeft.getSubExpr(3), tRight.getSubExpr(3));

		            /*
					TODO: this is sound if we assume that the first element of a tuple is the sound identifier.
						  does this make sense? it should be advantageous to use the other tuple components to differentiate objects
						  (also applies to case StringEq)
					*/
		            return p.mkEq(tLeft.getSubExpr(0), tRight.getSubExpr(0));
		        } else {
					return p.mkEq(left, right);
		        }
			case Ne:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;
					//if( tLeft.getSubExpr(3).getType() ==
					/*if(tLeft.getSubExpr(3) instanceof PrincessADTType)
					{*/
					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint"))
							return p.mkNot( p.mkEq(tLeft.getSubExpr(3), tRight.getSubExpr(3)));
					//}
				}

				return p.mkNot(p.mkEq(left, right));
			case Gt:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;
					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));
							return p.mkIte(p.mkEq(leftSign,rightSign),
									p.mkIte(p.mkEq(leftExponent,rightExponent),
											p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUlt(leftMantisa,rightMantisa),p.mkBVUgt(leftMantisa,rightMantisa)),
											p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUlt(leftExponent,rightExponent),p.mkBVUgt(leftExponent,rightExponent))),
									p.mkIte(p.mkBVUlt(leftSign,rightSign),p.mkLiteral(true),p.mkLiteral(false))
							);

						}
				}
				return p.mkGt(left, right);
			case Ge:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;
					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));
							return p.mkIte(p.mkEq(tLeft.getSubExpr(3), tRight.getSubExpr(3)),
									p.mkLiteral(true),
									p.mkIte(p.mkEq(leftSign,rightSign),
											p.mkIte(p.mkEq(leftExponent,rightExponent),
													p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUlt(leftMantisa,rightMantisa),p.mkBVUgt(leftMantisa,rightMantisa)),
													p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUlt(leftExponent,rightExponent),p.mkBVUgt(leftExponent,rightExponent))),
											p.mkIte(p.mkBVUlt(leftSign,rightSign),p.mkLiteral(true),p.mkLiteral(false))
									)
							);
							/*return p.mkBVLeq(FloatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3)),
									FloatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3)));*/
						}
				}
				return p.mkGeq(left, right);
			case Lt:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;
					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));
							return p.mkIte(p.mkEq(leftSign,rightSign),
											p.mkIte(p.mkEq(leftExponent,rightExponent),
													p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUgt(leftMantisa,rightMantisa),p.mkBVUlt(leftMantisa,rightMantisa)),
													p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)), p.mkBVUgt(leftExponent,rightExponent),p.mkBVUlt(leftExponent,rightExponent))),
											p.mkIte(p.mkBVUlt(leftSign,rightSign),p.mkLiteral(false),p.mkLiteral(true))
									);

						}
				}
				return p.mkLt(left, right);
			case Le:
				if (left instanceof ProverTupleExpr) {
					ProverTupleExpr tLeft = (ProverTupleExpr)left;
					ProverTupleExpr tRight = (ProverTupleExpr)right;
					if(tLeft.getArity() == 4)
						if(((PrincessADTType)tLeft.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr leftSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tLeft.getSubExpr(3));
							ProverExpr leftExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tLeft.getSubExpr(3));
							ProverExpr leftMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tLeft.getSubExpr(3));
							ProverExpr rightSign = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 0, tRight.getSubExpr(3));
							ProverExpr rightExponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tRight.getSubExpr(3));
							ProverExpr rightMantisa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tRight.getSubExpr(3));
							return p.mkIte(p.mkEq(tLeft.getSubExpr(3), tRight.getSubExpr(3)),
									       p.mkLiteral(true),
									       p.mkIte(p.mkEq(leftSign,rightSign),
												   p.mkIte(p.mkEq(leftExponent,rightExponent),
														   p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUgt(leftMantisa,rightMantisa),p.mkBVUlt(leftMantisa,rightMantisa)),
														   p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUgt(leftExponent,rightExponent),p.mkBVUlt(leftExponent,rightExponent))),
												   p.mkIte(p.mkBVUlt(leftSign,rightSign),p.mkLiteral(false),p.mkLiteral(true))
												   )
							);

						}
				}
				return p.mkLeq(left, right);
			case PoLeq:
				if ((be.getRight() instanceof IdentifierExpression)
						&& (((IdentifierExpression) be.getRight()).getVariable() instanceof ClassVariable)) {
					final ClassVariable var = (ClassVariable) ((IdentifierExpression) be.getRight()).getVariable();

					ProverExpr disj = p.mkLiteral(false);
					for (Integer i : this.hornContext.getSubtypeIDs(var)) {
						// ProverExpr tmp =
						// p.mkTupleSelect(typeIdToProverExpr(i), 0);
						ProverExpr tmp = typeIdToProverExpr(i);
						disj = p.mkOr(disj, p.mkEq(left, tmp));
					}

					return disj;
				} else {
					throw new RuntimeException("instanceof is only supported for concrete types");
				}
			case And:
				return p.mkAnd(left, right);
			case Or:
				return p.mkOr(left, right);
			case Implies:
				return p.mkImplies(left, right);
			case IndexInString:
				return stringEncoder.mkIndexInString(e, varMap);
			case Shl:
			case Shr:
			case Ushr:
			case BAnd:
			case BOr:
			case Xor:
                                if (hornContext.elimOverApprox())
                                    throw new OverApproxException();
				return p.mkHornVariable("HACK_FreeVar" + HornHelper.hh().newVarNum(), p.getIntType());
			// Verify.verify(left.getType()==p.getIntType() &&
			// right.getType()==p.getIntType());
			// return binopFun.mkExpr(new ProverExpr[]{left, right});
			default: {
				throw new RuntimeException("Not implemented for " + be.getOp());
			}
			}
		} else if (e instanceof UnaryExpression) {
			final UnaryExpression ue = (UnaryExpression) e;
			final ProverExpr subExpr = exprToProverExpr(ue.getExpression(), varMap);

			/*
			TODO: the following choices encode Java semantics
				  of various operators; need a good schema to choose
				  how precise the encoding should be (probably
				  configurable)
			*/
			switch (ue.getOp()) {
			case Neg:
				return p.mkNeg(subExpr);
			case LNot:
				return p.mkNot(subExpr);
			case ABS:
				if (subExpr instanceof ProverTupleExpr) {
					ProverTupleExpr tSubExpr = (ProverTupleExpr) subExpr;
					if (tSubExpr.getArity() == 4)
						if (((PrincessADTType) tSubExpr.getSubExpr(3).getType()).sort.name().equals("DoubleFloatingPoint")) {
							//final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
							ProverExpr exponent = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 1, tSubExpr.getSubExpr(3));
							ProverExpr mantissa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tSubExpr.getSubExpr(3));
							//ProverExpr mantissa = doubleFloatingPointEnCoder.getFloatingPointADT().mkSelExpr(0, 2, tSubExpr.getSubExpr(3));
							return p.mkTuple(new ProverExpr[]{tSubExpr.getSubExpr(0), tSubExpr.getSubExpr(1), tSubExpr.getSubExpr(2)
									, doubleFloatingPointEnCoder.mkDoublePE(p.mkBV(0, 1), exponent, mantissa)});
						}
					return p.mkIte(p.mkAnd(p.mkLeq(subExpr, p.mkLiteral(0)), p.mkNot(p.mkEq(subExpr, p.mkLiteral(0)))), p.mkNeg(subExpr), subExpr);
				}

			}
		} else if (e instanceof IteExpression) {
			final IteExpression ie = (IteExpression) e;

			final ProverExpr condExpr = exprToProverExpr(ie.getCondition(), varMap);
			final ProverExpr thenExpr = exprToProverExpr(ie.getThenExpr(), varMap);
			final ProverExpr elseExpr = exprToProverExpr(ie.getElseExpr(), varMap);
			return p.mkIte(condExpr, thenExpr, elseExpr);
		} else if (e instanceof BooleanLiteral) {
			return p.mkLiteral(((BooleanLiteral) e).getValue());
		}
		throw new RuntimeException("Expression type " + e + " not implemented!");
	}

	
        /**
         * For variables representing global constants, generate a unique reference
         * based on the index of the variable.
         */
        private ProverExpr makeUniqueReference(Prover p, Variable v,
                                               ProverExpr fullRef, int number) {
		ProverType pt = HornHelper.hh().getProverType(p, v.getType());
		if (pt instanceof ProverTupleType) {
                        Verify.verify(v.getType() instanceof ReferenceType);
                        final ClassVariable classVar =
                            ((ReferenceType)v.getType()).getClassVariable();
                        final ProverExpr classId =
                            typeIdToProverExpr(hornContext.getTypeID(classVar));
                        return
                            p.mkTupleUpdate(
                            p.mkTupleUpdate(fullRef,
                                            0, p.mkLiteral(number)),
                                            1, classId);
		} else if (pt instanceof jayhorn.solver.IntType) {
			return p.mkLiteral(number);
		} else {
			Verify.verify(false);
                        return fullRef;
		}
        }

}
