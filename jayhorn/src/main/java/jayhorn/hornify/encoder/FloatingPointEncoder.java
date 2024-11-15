package jayhorn.hornify.encoder;

import com.google.common.base.Verify;

import jayhorn.hornify.HornHelper;
import jayhorn.hornify.HornPredicate;
import jayhorn.hornify.WrappedProverType;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessADTType;
import jayhorn.solver.princess.PrincessFloatingPointADTFactory;
import jayhorn.solver.princess.PrincessFloatingPointType;
import scala.Int;
import soottocfg.cfg.expression.*;
import soottocfg.cfg.expression.literal.DoubleLiteral;
import soottocfg.cfg.expression.literal.FloatLiteral;
import soottocfg.cfg.expression.literal.StringLiteral;
import soottocfg.cfg.type.*;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.variable.Variable;

import javax.annotation.Nullable;
import java.awt.datatransfer.FlavorListener;
import java.math.BigInteger;
import java.util.*;

public class FloatingPointEncoder {

    private ExpressionEncoder expEncoder;

    public enum Precision {
        Single,
        Double
    }

    private Prover p;
    private ProverADT floatingPointADT;
    private ProverADT extendedFloatingPointADT;

    private ProverFun xORSigns;

    private ProverFun isOVFExp;

    private ProverFun isUDFExp;
    private ProverFun isOVFSigInAdd;

    private ProverFun isOVFSigInMul;

    private ProverFun extractSigLSBInMul;

    private ProverFun extractSigGInMul;

    private ProverFun extractSigRInMul;

    private ProverFun computeStickyInMul;

    private ProverFun requiredRoundingUp;

    private ProverFun roundingUPInMul;

    private ProverFun makeOVFFun;

    private ProverFun makeUDFFun;

    private ProverFun existZeroFun;
    private ProverFun existInfFun;
    private ProverFun existNaNFun;

    private ProverFun operandsEqInfFun;

    private ProverFun operandsEqZeroFun;

    private ProverFun isNegFun;
    private ProverFun areEqSignsFun;

    private ProverFun isInf;
    private ProverFun isNaN;

    private ProverFun makeNANFun;

    private ProverFun makeInfFun;
    private ProverFun negateFun;

    private ProverFun existSpecCasInMul;


    private ProverADT tempFloatingPointOperandsADT;

    private Precision floatingPointPrecision;

    public ProverADT getFloatingPointADT() {
        return floatingPointADT;
    }

    public ProverADT getTempFloatingPointADT() {
        return extendedFloatingPointADT;
    }

    public ProverADT getTempFloatingPointOperandsADT() {
        return tempFloatingPointOperandsADT;
    }

    public ProverFun getxORSigns() {
        return xORSigns;
    }

    private int f, e;

    public static class EncodingFacts {
        final ProverExpr rely, guarantee, result, constraint;

        public EncodingFacts(ProverExpr rely, ProverExpr guarantee, ProverExpr result, ProverExpr constraint) {
            this.rely = rely;               // preAtom => rely
            this.guarantee = guarantee;     // constraint & guarantee? & preAtom => postAtom
            this.result = result;           // varMap.put(lhs.var, result)
            this.constraint = constraint;
        }
    }

    public List<ProverHornClause> handleFloatingPointExpr(Expression e, IdentifierExpression idLhs, Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom, ExpressionEncoder expEnc) {
        expEncoder = expEnc;

        if (e instanceof BinaryExpression) {
            final BinaryExpression be = (BinaryExpression) e;
            Expression leftExpr = be.getLeft();
            Expression rightExpr = be.getRight();
            if(((PrincessADTType)floatingPointADT.getType(0)).sort.name().equals("DoubleFloatingPoint")) {
                if (rightExpr instanceof FloatLiteral) return null;
            }
            switch (be.getOp()) {
                case ToDouble:
                case ToFloat:
                    return mkToDoubleFromExpression(leftExpr, idLhs, rightExpr, varMap, postPred, prePred, preAtom);
                case AssumeFloat:

                case AssumeDouble:
                    return mkAssumeDoubleFromExpression(rightExpr, varMap, postPred, prePred, preAtom);
                case MulDouble:
                    return mkMulDoubleFromExpression2(leftExpr, idLhs, rightExpr, varMap, postPred, prePred, preAtom);
                case MulFloat:
                    return floatMulFromExp2(leftExpr, idLhs, rightExpr, varMap, postPred, prePred, preAtom);
                case AddDouble:
                    ProverExpr left = expEncoder.exprToProverExpr(leftExpr, varMap);
                    ProverExpr right = expEncoder.exprToProverExpr(rightExpr, varMap);
                    return mkAddDoubleFromExpression2(left, idLhs, right, varMap, postPred, prePred, preAtom);
                case MinusDouble:
                    left = expEncoder.exprToProverExpr(leftExpr, varMap);
                    right = expEncoder.exprToProverExpr(rightExpr, varMap);
                    ProverTupleExpr tright = (ProverTupleExpr) right;
                    ProverExpr rightFloatingPointADT = tright.getSubExpr(3);
                    ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, rightFloatingPointADT);
                    ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, rightFloatingPointADT);// FloatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
                    ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, rightFloatingPointADT);
                    ProverExpr rightIsNan = floatingPointADT.mkSelExpr(0, 3, rightFloatingPointADT);
                    ProverExpr rightIsInf = floatingPointADT.mkSelExpr(0, 4, rightFloatingPointADT);
                    ProverExpr rightOVF = floatingPointADT.mkSelExpr(0, 5, rightFloatingPointADT);
                    ProverExpr rightUDF = floatingPointADT.mkSelExpr(0, 6, rightFloatingPointADT);
                    ProverExpr negatedRight = p.mkTupleUpdate(tright, 3, mkDoublePE(p.mkNot(rightSign), rightExponent, rightMantisa, rightIsNan, rightIsInf,rightOVF,rightUDF));
                    return mkAddDoubleFromExpression2(left, idLhs, negatedRight, varMap, postPred, prePred, preAtom);
                case MinusFloat:
                    return null;

                default:
                    return null;

            }
        } else if (e instanceof UnaryExpression) {
            final UnaryExpression ue = (UnaryExpression) e;
            final ProverExpr subExpr = expEnc.exprToProverExpr(ue.getExpression(), varMap);
            switch (ue.getOp()) {
                case NegDouble:
                    break;
                case NegFloat:
                    break;
                default:
                    return null;
            }
        } else if (e instanceof IteExpression) {
            final IteExpression ie = (IteExpression) e;

            final BinaryExpression condExpr = (BinaryExpression) ie.getCondition();
            final BinaryExpression be = (BinaryExpression) condExpr;
            Expression leftExpr = be.getLeft();
            Expression rightExpr = be.getRight();
            if(((PrincessADTType)floatingPointADT.getType(0)).sort.name().equals("DoubleFloatingPoint")) {
                if (rightExpr instanceof FloatLiteral) return null;
            }
            final ProverExpr thenExpr = expEncoder.exprToProverExpr(ie.getThenExpr(), varMap);
            final ProverExpr elseExpr = expEncoder.exprToProverExpr(ie.getElseExpr(), varMap);

            //ProverExpr finalExpr = p.mkIte(condExpr, thenExpr, elseExpr);
            switch (be.getOp()) {
                case LeDouble:
                    return mkLeDoubleFromExpression(leftExpr, idLhs, rightExpr, varMap, postPred, prePred, preAtom, thenExpr, elseExpr);
                    case LeFloat:
                        return floatLeFromExp(leftExpr, idLhs, rightExpr, varMap, postPred, prePred, preAtom, thenExpr, elseExpr);
                default:
                    return null;
            }
        }
        return null;
    }

    public List<ProverHornClause> mkNegDoubleFromExpression() {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();


        return clauses;

    }

    public List<ProverHornClause> mkAssumeDoubleFromExpression(Expression rightExpr, Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
      /*  if(rightExpr instanceof BinaryExpression && ((BinaryExpression) rightExpr).getOp() == BinaryExpression.BinaryOperator.And)
        {
            final ProverExpr leftCond = expEncoder.exprToProverExpr(((BinaryExpression) rightExpr).getLeft(), varMap);

            final HornPredicate leftCondPred = new HornPredicate(p, prePred.name + "_1", prePred.variables);
            final ProverExpr leftCondAtom = leftCondPred.instPredicate(varMap);
            clauses.add(p.mkHornClause(leftCondAtom, new ProverExpr[]{preAtom}, leftCond));

            final ProverExpr rightCond = expEncoder.exprToProverExpr(((BinaryExpression) rightExpr).getRight(), varMap);
            final ProverExpr postAtom = postPred.instPredicate(varMap);
            clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{leftCondAtom}, rightCond));
        }*/
        final ProverExpr leftCond = expEncoder.exprToProverExpr(((BinaryExpression) rightExpr).getLeft(), varMap);

        final HornPredicate leftCondPred = new HornPredicate(p, prePred.name + "_1", prePred.variables);
        final ProverExpr leftCondAtom = leftCondPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(leftCondAtom, new ProverExpr[]{preAtom}, leftCond));

        final ProverExpr rightCond = expEncoder.exprToProverExpr(((BinaryExpression) rightExpr).getRight(), varMap);
        final ProverExpr postAtom = postPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{leftCondAtom}, rightCond));
        //((BinaryExpression) ((BinaryExpression) rightExpr).getLeft()).getRight().getUseVariables()
       /* final ProverExpr expr1 =  expEncoder.exprToProverExpr(((BinaryExpression) ((BinaryExpression) rightExpr).getLeft()).getRight(), varMap);
        final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);



        final ProverExpr boundCond = expEncoder.exprToProverExpr(((BinaryExpression) rightExpr), varMap);
        final ProverExpr notNanAndInfinity = p.mkNot(p.mkEq(FloatingPointADT.mkSelExpr(0, 1, ((ProverTupleExpr)expr1).getSubExpr(3)),p.mkBV(((int)Math.pow(2.0,11.0))-1,11)));

                //p.mkBVUlt(FloatingPointADT.mkSelExpr(0, 1, ((ProverTupleExpr)expr1).getSubExpr(3)),p.mkBV(((int)Math.pow(2.0,11.0))-1,11));// p.mkNot(p.mkEq(FloatingPointADT.mkSelExpr(0, 1, ((ProverTupleExpr)expr1).getSubExpr(3)),p.mkBV(((int)Math.pow(2.0,11.0))-1,11)));
        //final ProverExpr beNormal = p.mkNot(p.mkEq(p.mkBVExtract(52,52,FloatingPointADT.mkSelExpr(0, 2, ((ProverTupleExpr)expr1).getSubExpr(3))),p.mkBV(0,1)));
       //inal ProverExpr finalCond = p.mkAnd(notNanAndInfinity,beNormal,boundCond);

        final ProverExpr postAtom = postPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, boundCond));*/
        return clauses;

    }

    public List<ProverHornClause> mkAssumeFloatFromExpression(Expression rightExpr, Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();

        return clauses;
    }

    public List<ProverHornClause> mkToDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                           Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) lhsRefExpr.getType();

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr resultDouble = selectFloatingPoint(result);

        varMap.put(idLhs.getVariable(), result);
        ProverExpr[] body = new ProverExpr[]{preAtom};

        final ProverExpr postAtom = postPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom, body,
                p.mkAnd(mkNotNullConstraint(result),
                        p.mkEq(resultDouble, internalDouble))));

        return clauses;
    }

    public List<ProverHornClause> mkLeDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                           Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom, ProverExpr thenExpr, ProverExpr elseExpr) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof DoubleLiteral ? ((DoubleLiteral) lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr) left;
        ProverTupleExpr tRight = (ProverTupleExpr) right;

        //final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);

        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        ProverExpr Cond = p.mkNot(p.mkEq(((ProverTupleExpr) left).getSubExpr(3), ((ProverTupleExpr) right).getSubExpr(3)));
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));
        //-----------------------------------------------------------------------------------------------------


        List<Variable> postPred2Vars = new ArrayList<>(prePred.variables);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);
        Cond = p.mkEq(leftSign, rightSign);
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond));
        //-----------------------------------------------------------------------------------------------------

        varMap.put(idLhs.getVariable(), p.mkIte(p.mkAnd(p.mkEq(leftSign, p.mkLiteral(1)), p.mkEq(rightSign, p.mkLiteral(0))), thenExpr, elseExpr));
        ProverExpr postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftSign, rightSign));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond));

        varMap.put(idLhs.getVariable(), p.mkIte(p.mkIte(p.mkEq(leftSign, p.mkLiteral(1)), p.mkBVUgt(leftMantisa, rightMantisa), p.mkBVUlt(leftMantisa, rightMantisa)), thenExpr, elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(leftExponent, rightExponent);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.replace(idLhs.getVariable(), varMap.get(idLhs.getVariable()), p.mkIte(p.mkIte(p.mkEq(leftSign, p.mkLiteral(1)), p.mkBVUgt(leftExponent, rightExponent), p.mkBVUlt(leftExponent, rightExponent)), thenExpr, elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftExponent, rightExponent));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.put(idLhs.getVariable(), thenExpr);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(((ProverTupleExpr) left).getSubExpr(3), ((ProverTupleExpr) right).getSubExpr(3));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        return clauses;
    }
    public List<ProverHornClause> floatLeFromExp(Expression FloatExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                           Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom, ProverExpr thenExpr, ProverExpr elseExpr) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof FloatLiteral ? ((FloatLiteral) lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalFloat = selectFloatingPoint(FloatExpr, varMap);
        if (internalFloat == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalFloat.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(FloatExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr) left;
        ProverTupleExpr tRight = (ProverTupleExpr) right;

        //final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);

        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        ProverExpr Cond = p.mkNot(p.mkEq(((ProverTupleExpr) left).getSubExpr(3), ((ProverTupleExpr) right).getSubExpr(3)));
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));
        //-----------------------------------------------------------------------------------------------------


        List<Variable> postPred2Vars = new ArrayList<>(prePred.variables);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);
        Cond = p.mkEq(leftSign, rightSign);
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond));
        //-----------------------------------------------------------------------------------------------------

        varMap.put(idLhs.getVariable(), p.mkIte(p.mkAnd(p.mkEq(leftSign, p.mkLiteral(1)), p.mkEq(rightSign, p.mkLiteral(0))), thenExpr, elseExpr));
        ProverExpr postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftSign, rightSign));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond));

        varMap.put(idLhs.getVariable(), p.mkIte(p.mkIte(p.mkEq(leftSign, p.mkLiteral(1)), p.mkBVUgt(leftMantisa, rightMantisa), p.mkBVUlt(leftMantisa, rightMantisa)), thenExpr, elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(leftExponent, rightExponent);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.replace(idLhs.getVariable(), varMap.get(idLhs.getVariable()), p.mkIte(p.mkIte(p.mkEq(leftSign, p.mkLiteral(1)), p.mkBVUgt(leftExponent, rightExponent), p.mkBVUlt(leftExponent, rightExponent)), thenExpr, elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftExponent, rightExponent));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.put(idLhs.getVariable(), thenExpr);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(((ProverTupleExpr) left).getSubExpr(3), ((ProverTupleExpr) right).getSubExpr(3));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        return clauses;
    }

    public List<ProverHornClause> mkAddDoubleFromExpression2(ProverExpr left, IdentifierExpression idLhs, ProverExpr right,
                                                             Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();


       /* ProverTupleExpr tLeft = (ProverTupleExpr)left;
        ProverTupleExpr tRight = (ProverTupleExpr)right;
        ProverExpr leftFloatingPointADT = tLeft.getSubExpr(3);
        ProverExpr rightFloatingPointADT = tRight.getSubExpr(3);

       // final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, leftFloatingPointADT);
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, leftFloatingPointADT);
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, leftFloatingPointADT);
        ProverExpr leftIsNan = floatingPointADT.mkSelExpr(0, 3, leftFloatingPointADT);
        ProverExpr leftIsInf = floatingPointADT.mkSelExpr(0, 4, leftFloatingPointADT);
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, rightFloatingPointADT);
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, rightFloatingPointADT);// FloatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, rightFloatingPointADT);
        ProverExpr rightIsNan = floatingPointADT.mkSelExpr(0, 3, rightFloatingPointADT);
        ProverExpr rightIsInf = floatingPointADT.mkSelExpr(0, 4, rightFloatingPointADT);

        // Check for special cases

        ProverExpr bothZero = p.mkEq(p.mkBVOR(leftExponent,rightExponent,11),p.mkBV(0,11) );
        ProverExpr noNaNInf = p.mkNot(p.mkEq(p.mkBVOR(leftExponent,rightExponent,11),p.mkBV(1,11) ));
        ProverExpr bothInf = p.mkAnd(p.mkEq(leftIsInf,p.mkLiteral(1)), p.mkEq(rightIsInf,p.mkLiteral(1)));
        ProverExpr sameSigns = p.mkEq(leftSign,rightSign);
        ProverExpr negativeSign = p.mkLiteral(1);
        ProverExpr postiveSign = p.mkLiteral(0);
        ProverExpr isLeftpostive = p.mkEq(leftSign,postiveSign);
        ProverExpr isRightpostive = p.mkEq(rightSign,postiveSign);
        ProverExpr NaNMantissa = p.mkBV(new BigInteger("9007199254740991"),53) ;
        ProverExpr NaNDoubleFADT = mkDoublePE(postiveSign,p.mkBV(2047,11),NaNMantissa,p.mkLiteral(1), p.mkLiteral(0));


        // 0 + 0
        //pre ^ bothZeros --> post(if sameSigns then left else +0)

        ProverExpr idLhsExpr = varMap.get(idLhs.getVariable());
        ProverTupleExpr idLhsTExpr = (ProverTupleExpr)  idLhsExpr;
        ProverExpr addResult =p.mkTupleUpdate(idLhsTExpr,3,
                p.mkIte(sameSigns,
                leftFloatingPointADT,
                mkDoublePE(postiveSign,leftExponent,leftMantisa, leftIsNan, leftIsInf)));
        varMap.put(idLhs.getVariable(),addResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);
        ProverExpr Cond = bothZero;
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        // +Inf - Inf or -Inf + Inf or There is at least a NAN
        //pre ^ (bothInf ^ !sameSign) --> post(NAN)
        addResult = p.mkTupleUpdate(idLhsTExpr,3, NaNDoubleFADT);
        varMap.put(idLhs.getVariable(),addResult);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkOr(p.mkEq(leftIsNan,p.mkLiteral(1)),p.mkEq(rightIsNan, p.mkLiteral(1)), p.mkAnd(bothInf,p.mkNot(sameSigns)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        // both are Inf with same signs
        // pre ^ (bothInf ^ sameSign) --> post(left)
        addResult = p.mkTupleUpdate(idLhsTExpr,3, leftFloatingPointADT);
        varMap.put(idLhs.getVariable(),addResult);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkAnd(p.mkEq(leftIsInf,p.mkLiteral(1)),p.mkEq(rightIsInf,p.mkLiteral(1)),sameSigns);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        // There is an Inf and NaN is not exist
        // pre ^ (!leftIsNaN ^ !rightIsNaN) ^ (LeftIsInf XOR RightIsInf) --> post(if leftIsInf then left else right)
        addResult = p.mkTupleUpdate(idLhsTExpr,3, p.mkIte(leftIsInf, leftFloatingPointADT,rightFloatingPointADT));
        varMap.put(idLhs.getVariable(),addResult);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkAnd(p.mkNot(leftIsNan), p.mkNot(rightIsNan),
                p.mkOr(p.mkAnd(leftIsInf,p.mkNot(rightIsInf)),p.mkAnd(p.mkNot(leftIsInf),rightIsInf)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));



       //ADD
        ProverExpr ZeroExtendedLeftM = p.mkBVZeroExtend(1,leftMantisa,53);
        ProverExpr ZeroExtendedRightM = p.mkBVZeroExtend(1,rightMantisa,53);
        ProverExpr eLeft_eRight_diff = p.mkBVSub(leftExponent,rightExponent,11);



        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);

        Variable doubleFPOperands = new Variable("doubleFPOperands", new WrappedProverType(tempFloatingPointOperandsADT.getType(0)));
        Variable exponentsDiff = new Variable("exponentsDiff",  Type.instance(),11);
        postPred1Vars.add(doubleFPOperands);
        postPred1Vars.add(exponentsDiff);
        ProverExpr tempDoubleLeft = mkTempDoublePE(leftFloatingPointADT);
        ProverExpr tempDoubleRight = mkTempDoublePE(rightFloatingPointADT);
        varMap.put(doubleFPOperands,mkTempDoublePEFromOperands(tempDoubleLeft, tempDoubleRight));
        varMap.put(exponentsDiff,eLeft_eRight_diff);

        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);

        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        Cond = p.mkAnd(p.mkNot(bothZero), noNaNInf);
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));


        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        postAtom1 = postPred1.instPredicate(varMap);

        List<Variable> postPred2Vars = new ArrayList<>(postPred1.variables);
        postPred2Vars.remove(exponentsDiff);
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr isPositiveEDiff = p.mkEq(p.mkBVExtract(10,10,varMap.get(exponentsDiff)),p.mkBV(0,1));
        ProverExpr leftOperand = tempFloatingPointOperandsADT.mkSelExpr(0,0,varMap.get(doubleFPOperands));
        ProverExpr signLeftOperand = tempFloatingPointADT.mkSelExpr(0,0,leftOperand);
        ProverExpr exponentLeftOperand = tempFloatingPointADT.mkSelExpr(0,1,leftOperand);
        ProverExpr mantissaLeftOperand = tempFloatingPointADT.mkSelExpr(0,2,leftOperand);
        ProverExpr isNaNLeftOperand = tempFloatingPointADT.mkSelExpr(0,3,leftOperand);
        ProverExpr isInfLeftOperand = tempFloatingPointADT.mkSelExpr(0,4,leftOperand);
        ProverExpr rightOperand = tempFloatingPointOperandsADT.mkSelExpr(0,1,varMap.get(doubleFPOperands));
        ProverExpr signRightOperand = tempFloatingPointADT.mkSelExpr(0,0,rightOperand);
        ProverExpr exponentRightOperand = tempFloatingPointADT.mkSelExpr(0,1,rightOperand);
        ProverExpr mantissaRightOperand = tempFloatingPointADT.mkSelExpr(0,2,rightOperand);
        ProverExpr isNaNRightOperand = tempFloatingPointADT.mkSelExpr(0,3,rightOperand);
        ProverExpr isInfRightOperand = tempFloatingPointADT.mkSelExpr(0,4,rightOperand);

        ProverExpr shiftedLeftOperand = mkTempDoublePE(signLeftOperand,exponentRightOperand,p.mkBVlshr(mantissaLeftOperand,p.mkBVZeroExtend(44,p.mkBVNeg(varMap.get(exponentsDiff),11),11),55),isNaNLeftOperand,isInfLeftOperand);
        ProverExpr shiftedRightOperand = mkTempDoublePE(signRightOperand,exponentLeftOperand,p.mkBVlshr(mantissaRightOperand,p.mkBVZeroExtend(44,varMap.get(exponentsDiff) ,11),55),isNaNRightOperand,isInfRightOperand);
        varMap.put(doubleFPOperands,p.mkIte(isPositiveEDiff,mkTempDoubleOperandsPE(leftOperand,shiftedRightOperand),mkTempDoubleOperandsPE(shiftedLeftOperand,rightOperand)));
        varMap.remove(exponentsDiff);

        ProverExpr postAtom2 = postPred2.instPredicate(varMap);

        Cond = p.mkLiteral(true);
        // post1 --> post2
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond));


        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);
        postAtom2 = postPred2.instPredicate(varMap);

         leftOperand = tempFloatingPointOperandsADT.mkSelExpr(0,0,varMap.get(doubleFPOperands));
         signLeftOperand = tempFloatingPointADT.mkSelExpr(0,0,leftOperand);
         exponentLeftOperand = tempFloatingPointADT.mkSelExpr(0,1,leftOperand);
         mantissaLeftOperand = tempFloatingPointADT.mkSelExpr(0,2,leftOperand);
         isNaNLeftOperand = tempFloatingPointADT.mkSelExpr(0,3,leftOperand);
         isInfLeftOperand = tempFloatingPointADT.mkSelExpr(0,4,leftOperand);
         rightOperand = tempFloatingPointOperandsADT.mkSelExpr(0,1,varMap.get(doubleFPOperands));
         signRightOperand = tempFloatingPointADT.mkSelExpr(0,0,rightOperand);
         exponentRightOperand = tempFloatingPointADT.mkSelExpr(0,1,rightOperand);
         mantissaRightOperand = tempFloatingPointADT.mkSelExpr(0,2,rightOperand);
         isNaNRightOperand = tempFloatingPointADT.mkSelExpr(0,3,rightOperand);
         isInfRightOperand = tempFloatingPointADT.mkSelExpr(0,4,rightOperand);

        List<Variable> postPred3Vars = new ArrayList<>(postPred2.variables);
        Variable tempDoubleFP = new Variable("tempDoubleFP", new WrappedProverType(tempFloatingPointADT.getType(0)));
        postPred3Vars.add(tempDoubleFP);
        postPred3Vars.remove(doubleFPOperands);
        HornHelper.hh().findOrCreateProverVar(p, postPred3Vars, varMap);
        HornPredicate postPred3 = new HornPredicate(p, prePred.name + "_3", postPred3Vars);
        varMap.put(tempDoubleFP,mkTempDoublePE(signLeftOperand,exponentLeftOperand,
                p.mkBVPlus(mantissaLeftOperand,mantissaRightOperand,55),isNaNLeftOperand,isInfLeftOperand));

        ProverExpr postAtom3 = postPred3.instPredicate(varMap);
        Cond = p.mkEq(signLeftOperand,signRightOperand);

        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond));

        //Do Addition
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred3Vars, varMap);
        postAtom3 = postPred3.instPredicate(varMap);

        ProverExpr tempDoubleFPEP = varMap.get(tempDoubleFP);
        ProverExpr signTemp = tempFloatingPointADT.mkSelExpr(0,0,tempDoubleFPEP);
        ProverExpr exponentTemp = tempFloatingPointADT.mkSelExpr(0,1,tempDoubleFPEP);
        ProverExpr mantissaTemp = tempFloatingPointADT.mkSelExpr(0,2,tempDoubleFPEP);
        ProverExpr isNaNTemp= tempFloatingPointADT.mkSelExpr(0,3,tempDoubleFPEP);
        ProverExpr isInfTemp = tempFloatingPointADT.mkSelExpr(0,4,tempDoubleFPEP);

        addResult = p.mkTupleUpdate(idLhsTExpr,3,
                p.mkIte(p.mkEq(p.mkBVExtract(53,53,mantissaTemp), p.mkBV(1,1)),
                        mkDoublePE(signTemp,p.mkBVPlus(exponentTemp, p.mkBV(1,11),11),p.mkBVPlus(p.mkBVExtract(53,1,mantissaTemp),p.mkBVZeroExtend(52,p.mkBVExtract(0,0,mantissaTemp),1),53), isNaNTemp,isInfTemp),
                        mkDoublePE(signTemp, exponentTemp, p.mkBVExtract(52,0,mantissaTemp),isNaNTemp,isInfTemp)
                        )
                );
        varMap.put(idLhs.getVariable(),addResult);
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkLiteral(true);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond));


        //Do subtraction
        List<Variable> postPred4Vars = new ArrayList<>(postPred3.variables);
        Variable leadingZerosCnt = new Variable("leadingZerosCnt",  Type.instance(),55);
        postPred4Vars.add(leadingZerosCnt);
        varMap.put(leadingZerosCnt,p.mkBV(0,55));
        HornHelper.hh().findOrCreateProverVar(p, postPred4Vars, varMap);
        HornPredicate postPred4 = new HornPredicate(p, prePred.name + "_4", postPred4Vars);
        varMap.put(tempDoubleFP,p.mkIte(p.mkBVUge(mantissaLeftOperand,mantissaRightOperand),
                mkTempDoublePE(signLeftOperand,exponentLeftOperand,p.mkBVSub(mantissaLeftOperand,mantissaRightOperand,55),isNaNLeftOperand,isInfRightOperand),
                mkTempDoublePE(signRightOperand,exponentLeftOperand,p.mkBVSub(mantissaRightOperand,mantissaLeftOperand,55),isNaNLeftOperand,isInfRightOperand))
                );
        ProverExpr postAtom4 = postPred4.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(signLeftOperand,signRightOperand));

        clauses.add(p.mkHornClause(postAtom4, new ProverExpr[]{postAtom2}, Cond));

        // Count leadingZeros
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred4Vars, varMap);
        postAtom4 = postPred4.instPredicate(varMap);

        tempDoubleFPEP = varMap.get(tempDoubleFP);
        signTemp = tempFloatingPointADT.mkSelExpr(0,0,tempDoubleFPEP);
        exponentTemp = tempFloatingPointADT.mkSelExpr(0,1,tempDoubleFPEP);
        mantissaTemp = tempFloatingPointADT.mkSelExpr(0,2,tempDoubleFPEP);
        isNaNTemp= tempFloatingPointADT.mkSelExpr(0,3,tempDoubleFPEP);
        isInfTemp = tempFloatingPointADT.mkSelExpr(0,4,tempDoubleFPEP);
        Cond = p.mkEq(p.mkBVExtract(52,52,varMap.get(tempDoubleFP)),p.mkBV(0,1));
        varMap.put(leadingZerosCnt, p.mkBVPlus(varMap.get(leadingZerosCnt),p.mkBV(1,55),55));
        varMap.put(tempDoubleFP,mkTempDoublePE(signTemp,exponentTemp,p.mkBVshl(mantissaTemp,p.mkBV(1,55),55),isNaNTemp,isInfTemp));
        ProverExpr postAtom4_1 = postPred4.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom4_1, new ProverExpr[]{postAtom4}, Cond));

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred4Vars, varMap);
        postAtom4 = postPred4.instPredicate(varMap);
        tempDoubleFPEP = varMap.get(tempDoubleFP);
         signTemp = tempFloatingPointADT.mkSelExpr(0,0,tempDoubleFPEP);
         exponentTemp = tempFloatingPointADT.mkSelExpr(0,1,tempDoubleFPEP);
         mantissaTemp = tempFloatingPointADT.mkSelExpr(0,2,tempDoubleFPEP);
         isNaNTemp= tempFloatingPointADT.mkSelExpr(0,3,tempDoubleFPEP);
         isInfTemp = tempFloatingPointADT.mkSelExpr(0,4,tempDoubleFPEP);
        Cond = p.mkEq(p.mkBVExtract(52,52,varMap.get(tempDoubleFP)),p.mkBV(1,1));
        ProverExpr subResult = p.mkTupleUpdate(idLhsTExpr,3,
                mkDoublePE(signTemp,
                        p.mkBVSub(exponentTemp,p.mkBVExtract(10,0,varMap.get(leadingZerosCnt)),11)
                        ,p.mkBVExtract(52,0,mantissaTemp),isNaNTemp,isInfTemp));
        varMap.put(idLhs.getVariable(),subResult);
        postAtom = postPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom4}, Cond));*/


        return clauses;
    }

    public List<ProverHornClause> mkAddDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                            Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof DoubleLiteral ? ((DoubleLiteral) lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr) left;
        ProverTupleExpr tRight = (ProverTupleExpr) right;

        // final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));// FloatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr ZeroExtendedLeftM = p.mkBVZeroExtend(1, leftMantisa, 53);
        ProverExpr ZeroExtendedRightM = p.mkBVZeroExtend(1, rightMantisa, 53);
        ProverExpr eLeft_eRight_diff = p.mkBVZeroExtend(43, p.mkBVSub(leftExponent, rightExponent, 11), 11);
        ProverExpr eRight_eLeft_diff = p.mkBVZeroExtend(43, p.mkBVSub(rightExponent, leftExponent, 11), 11);
        ProverExpr RightShiftedRightM = p.mkBVlshr(ZeroExtendedRightM, eLeft_eRight_diff, 54);
        ProverExpr RightShiftedleftM = p.mkBVlshr(ZeroExtendedLeftM, eRight_eLeft_diff, 54);

        Variable resultSignVar = new Variable("resultSignVar", Type.instance(), 1);
        Variable resultExponentVar = new Variable("resultExponentVar", Type.instance(), 11);
        Variable leftMantissaVar = new Variable("leftMantissaVar", Type.instance(), 54);
        Variable rightMantissaVar = new Variable("rightMantissaVar", Type.instance(), 54);


        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        postPred1Vars.add(resultSignVar);
        postPred1Vars.add(resultExponentVar);
        postPred1Vars.add(leftMantissaVar);
        postPred1Vars.add(rightMantissaVar);

        //varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        varMap.put(resultSignVar, leftSign);
        varMap.put(resultExponentVar, leftExponent/*p.mkBV(1019,11)*/);
        varMap.put(leftMantissaVar, ZeroExtendedLeftM);
        varMap.put(rightMantissaVar, RightShiftedRightM);
        //HornPredicate postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);

        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        ProverExpr Cond = p.mkBVUge(leftExponent, rightExponent);/*p.mkLiteral(true)*/
        ;
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));
        //----------------------------------------------------------------------------
        varMap.replace(resultExponentVar, varMap.get(resultExponentVar), rightExponent);
        varMap.replace(leftMantissaVar, varMap.get(leftMantissaVar), RightShiftedleftM);
        varMap.replace(rightMantissaVar, varMap.get(rightMantissaVar), ZeroExtendedRightM);

        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred1Vars);
        //postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);
        Cond = p.mkBVUlt(leftExponent, rightExponent);
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{preAtom}, Cond));

        //--------------------------------------------------------------------------

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1.variables, varMap);
        postAtom1 = postPred1.instPredicate(varMap);


        List<Variable> postPred2Vars = new ArrayList<>(postPred1Vars);
        Variable leadingZeroCountVar = new Variable("leadingZeroCountVar", Type.instance(), 53);
        Variable mantissaAddResVar = new Variable("mantissaAddResVar", Type.instance(), 54);
        postPred2Vars.remove(leftMantissaVar);
        postPred2Vars.remove(rightMantissaVar);
        postPred2Vars.add(mantissaAddResVar);
        postPred2Vars.add(leadingZeroCountVar);

        ProverExpr MantissaAdition = p.mkBVPlus(varMap.get(leftMantissaVar), varMap.get(rightMantissaVar), 54);/* p.mkBV(new BigInteger("10808639105689191"),54);*/
        varMap.put(leadingZeroCountVar, p.mkBV(0, 53));
        varMap.put(mantissaAddResVar, MantissaAdition);
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);


        HornPredicate postPred3 = new HornPredicate(p, prePred.name + "_3", postPred2Vars);
        ProverExpr postAtom3 = postPred3.instPredicate(varMap);
        Cond = p.mkLiteral(true);
        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom1}, Cond));


        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2.variables, varMap);
        postAtom2 = postPred2.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond));

       /* varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        postPred1Vars.remove(leadingZeroCountVar);
        postPred2Vars.remove(mantissaAddResVar);
        postPred2Vars.add(leftMantissaVar);
        postPred2Vars.add(rightMantissaVar);
        HornHelper.hh().findOrCreateProverVar(p, postPred10.variables, varMap);
        postAtom10 = postPred10.instPredicate(varMap);

        MantissaAdition = p.mkBV(new BigInteger("10808639105689191"),54);p.mkBVPlus(varMap.get(leftMantissaVar),varMap.get(rightMantissaVar),54);
        varMap.put(leadingZeroCountVar, p.mkBV(0,53));
        varMap.put(mantissaAddResVar,MantissaAdition );

        HornPredicate postPred20 =  new HornPredicate(p, prePred.name + "_20", postPred2Vars);
        ProverExpr postAtom20 = postPred20.instPredicate(varMap);
        Cond = p.mkLiteral(true);
        clauses.add(p.mkHornClause(postAtom20, new ProverExpr[]{postAtom10}, Cond));*/
        //--------------------------------------------------------------------------------------------------
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred3.variables, varMap);
       /* varMap.replace(leadingZeroCountVar,varMap.get(leadingZeroCountVar) ,createBVVariable(leadingZeroCountVar,53));
        varMap.replace(mantissaAddResVar,varMap.get(mantissaAddResVar),createBVVariable(mantissaAddResVar,54));*/
        Cond = p.mkEq(p.mkBVExtract(53, 53, varMap.get(mantissaAddResVar)), p.mkBV(0, 1));
        postAtom3 = postPred3.instPredicate(varMap);

        varMap.replace(leadingZeroCountVar, varMap.get(leadingZeroCountVar), p.mkBVPlus(varMap.get(leadingZeroCountVar), p.mkBV(1, 53), 53));
        varMap.replace(mantissaAddResVar, varMap.get(mantissaAddResVar), p.mkBVshl(varMap.get(mantissaAddResVar), p.mkBV(1, 54), 54));
        ProverExpr postAtom4 = postPred3.instPredicate(varMap);


        clauses.add(p.mkHornClause(postAtom4, new ProverExpr[]{postAtom3}, Cond));

        //-------------------------------------------------------------------------------------------------
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred3.variables, varMap);
       /* varMap.replace(leadingZeroCountVar,varMap.get(leadingZeroCountVar) ,createBVVariable(leadingZeroCountVar,53));
        varMap.replace(mantissaAddResVar,varMap.get(mantissaAddResVar),createBVVariable(mantissaAddResVar,54));*/
        postAtom3 = postPred3.instPredicate(varMap);

        HornHelper.hh().findOrCreateProverVar(p, postPred.variables, varMap);
        ProverExpr idLhsExpr = varMap.get(idLhs.getVariable());//expEncoder.exprToProverExpr(idLhs,varMap);
        ProverTupleExpr idLhsTExpr = (ProverTupleExpr) idLhsExpr;
        ProverExpr addResult = null;/*p.mkTupleUpdate(idLhsTExpr,3,mkDoublePE(varMap.get(resultSignVar),
                p.mkIte(p.mkEq(varMap.get(leadingZeroCountVar),p.mkBV(0,53)),

                        p.mkBVPlus(varMap.get(resultExponentVar),p.mkBV(1,11),11),
                        p.mkBVPlus( varMap.get(resultExponentVar), p.mkBVExtract(10,0, varMap.get(leadingZeroCountVar)),11)

                ),
                p.mkBVPlus(p.mkBVExtract(53,1,varMap.get(mantissaAddResVar)),p.mkBVZeroExtend(52,p.mkBVExtract(0,0,varMap.get(mantissaAddResVar)),1),53)
        ));*/
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult, 0, tLeft.getSubExpr(0));
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult, 1, tLeft.getSubExpr(1));
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult, 2, tLeft.getSubExpr(2));
        varMap.put(idLhs.getVariable(), addResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);

        Cond = p.mkEq(p.mkBVExtract(53, 53, varMap.get(mantissaAddResVar)), p.mkBV(1, 1));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond));

      /*  varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred20.variables, varMap);
        // postPred20 =  new HornPredicate(p, prePred.name + "_20", postPred2Vars);
       //  postAtom20 = postPred20.instPredicate(varMap);
      //  varMap.replace(leadingZeroCountVar,varMap.get(leadingZeroCountVar) ,createBVVariable(leadingZeroCountVar,53));
      //  varMap.replace(mantissaAddResVar,varMap.get(mantissaAddResVar),createBVVariable(mantissaAddResVar,54));
        postAtom20 = postPred20.instPredicate(varMap);
        HornHelper.hh().findOrCreateProverVar(p, postPred.variables, varMap);
        idLhsExpr = varMap.get(idLhs.getVariable());//expEncoder.exprToProverExpr(idLhs,varMap);
        idLhsTExpr = (ProverTupleExpr)  idLhsExpr;
        addResult = p.mkTupleUpdate(idLhsTExpr,3,mkDoublePE(varMap.get(resultSignVar),
                p.mkIte(p.mkEq(varMap.get(leadingZeroCountVar),p.mkBV(0,53)),

                        p.mkBVPlus(varMap.get(resultExponentVar),p.mkBV(1,11),11),
                        p.mkBVPlus(varMap.get(resultExponentVar), p.mkBVExtract(10,0, varMap.get(leadingZeroCountVar)),11)

                ),
                p.mkBVPlus(p.mkBVExtract(53,1,varMap.get(mantissaAddResVar)),p.mkBVZeroExtend(52,p.mkBVExtract(0,0,varMap.get(mantissaAddResVar)),1),53)
        ));
        varMap.put(idLhs.getVariable(),addResult);
        Cond = p.mkEq(p.mkBVExtract(53,53,varMap.get(mantissaAddResVar)),p.mkBV(1,1));
       postAtom3 = postPred.instPredicate(varMap);
        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom20}, Cond));*/

        return clauses;
    }

    public List<ProverHornClause> mkMinusDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                              Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof DoubleLiteral ? ((DoubleLiteral) lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr) left;
        ProverTupleExpr tRight = (ProverTupleExpr) right;

        // final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));// FloatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        return clauses;
    }

    public List<ProverHornClause> mkMulDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs, Expression lhsRefExpr,
                                                            Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom) {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof DoubleLiteral ? ((DoubleLiteral) lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr resultDouble = selectFloatingPoint(result);

        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);

        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr) left;
        ProverTupleExpr tRight = (ProverTupleExpr) right;
//floatingPointADT
        //final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr leftS_xor_rightS = p.mkBVXOR(leftSign, rightSign, 1);
        ProverExpr ZeroExtendedLeftM = p.mkBVZeroExtend(53, leftMantisa, 106);
        ProverExpr ZeroExtendedRightM = p.mkBVZeroExtend(53, rightMantisa, 106);
        ProverExpr leftePlusrighte_Sub_1023 = p.mkBVSub(p.mkBVPlus(leftExponent, rightExponent, 11),
                p.mkBV(1023, 11), 11);
        ProverExpr leftM_Mul_rightM = p.mkBVExtract(105, 51, p.mkBVMul(ZeroExtendedLeftM, ZeroExtendedRightM, 106));


        Variable resultSignVar = new Variable("resultSignVar", Type.instance(), 1);
        Variable exponentSub1023Var = new Variable("exponentSub1023Var", Type.instance(), 11);

        Variable mantissaMulResVar = new Variable("mantissaMulResVar", Type.instance(), 55);

        varMap.put(resultSignVar, leftS_xor_rightS);
        varMap.put(exponentSub1023Var, leftePlusrighte_Sub_1023);
        varMap.put(mantissaMulResVar, leftM_Mul_rightM);

        List<Variable> postPred1Vars = prePred.variables;
        postPred1Vars.add(resultSignVar);
        postPred1Vars.add(exponentSub1023Var);
        postPred1Vars.add(mantissaMulResVar);


        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, p.mkLiteral(true)));

        //----------------------------------------------------------------------------------------
        varMap.replace(resultSignVar, varMap.get(resultSignVar), createBVVariable(resultSignVar, 1));
        varMap.replace(exponentSub1023Var, varMap.get(exponentSub1023Var), createBVVariable(exponentSub1023Var, 11));
        varMap.replace(mantissaMulResVar, varMap.get(mantissaMulResVar), createBVVariable(mantissaMulResVar, 55));
        postAtom1 = postPred1.instPredicate(varMap);

        Variable mul_0 = new Variable("mul_0", Type.instance(), 1);
        Variable mul_1 = new Variable("mul_1", Type.instance(), 1);
        Variable mul_54 = new Variable("mul_54", Type.instance(), 1);
        Variable mul_53_1 = new Variable("mul_53_1", Type.instance(), 53);
        Variable mul_54_2 = new Variable("mul_54_2", Type.instance(), 53);
        ProverExpr extract_0_fromMul = p.mkBVExtract(0, 0, varMap.get(mantissaMulResVar));
        ProverExpr extract_1_fromMul = p.mkBVExtract(1, 1, varMap.get(mantissaMulResVar));
        ProverExpr extract_54_fromMul = p.mkBVExtract(54, 54, varMap.get(mantissaMulResVar));
        ProverExpr extract_53_1_fromMul = p.mkBVExtract(53, 1, varMap.get(mantissaMulResVar));
        ProverExpr extract_54_2_fromMul = p.mkBVExtract(54, 2, varMap.get(mantissaMulResVar));
        varMap.put(mul_0, extract_0_fromMul);
        varMap.put(mul_1, extract_1_fromMul);
        varMap.put(mul_54, extract_54_fromMul);
        varMap.put(mul_53_1, extract_53_1_fromMul);
        varMap.put(mul_54_2, extract_54_2_fromMul);
        varMap.remove(mantissaMulResVar);
        List<Variable> postPred2Vars = postPred1Vars;
        //postPred2Vars.add(resultSignVar);
        //postPred2Vars.add(exponentSub1023Var);
        postPred2Vars.add(mul_0);
        postPred2Vars.add(mul_1);
        postPred2Vars.add(mul_54);
        postPred2Vars.add(mul_53_1);
        postPred2Vars.add(mul_54_2);
        postPred1Vars.remove(mantissaMulResVar);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, p.mkLiteral(true)));

        //----------------------------------------------------------------------------------------
        varMap.replace(mul_0, varMap.get(mul_0), createBVVariable(mul_0, 1));
        varMap.replace(mul_1, varMap.get(mul_1), createBVVariable(mul_1, 1));
        varMap.replace(mul_54, varMap.get(mul_54), createBVVariable(mul_54, 1));
        varMap.replace(mul_53_1, varMap.get(mul_53_1), createBVVariable(mul_53_1, 53));
        varMap.replace(mul_54_2, varMap.get(mul_54_2), createBVVariable(mul_54_2, 53));
        postAtom2 = postPred2.instPredicate(varMap);


        ProverExpr Cond = p.mkEq(varMap.get(mul_54), p.mkBV(1, 1));

        ProverExpr mulResult = null;/*p.mkTuple(new ProverExpr[]{tLeft.getSubExpr(0), tLeft.getSubExpr(1), tLeft.getSubExpr(2)
                , mkDoublePE(
                        varMap.get(resultSignVar), //sign
                       p.mkBVPlus(varMap.get(exponentSub1023Var),p.mkBV(1,11),11), //exponnet
                       p.mkBVPlus(varMap.get(mul_54_2),p.mkBVZeroExtend(52,varMap.get(mul_1),53),53)
                )
        });*/

        varMap.put(idLhs.getVariable(), mulResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));
        //----------------------------------------------------------------------------------------

       /* Cond = p.mkEq(varMap.get(mul_54),p.mkBV(0,1));

         mulResult = p.mkTuple(new ProverExpr[]{tLeft.getSubExpr(0), tLeft.getSubExpr(1), tLeft.getSubExpr(2)
                , mkDoublePE(
                varMap.get(resultSignVar), //sign
                varMap.get(exponentSub1023Var), //exponnet
                p.mkBVPlus(varMap.get(mul_53_1),p.mkBVZeroExtend(52,varMap.get(mul_0),53),53)
        )
        });

        varMap.replace(idLhs.getVariable(),varMap.get(idLhs.getVariable()),mulResult);
         postAtom = postPred.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));*/

        return clauses;
    }

    private ProverExpr XORSigns(ProverExpr lFP, ProverExpr rFP)
    {
        return xORSigns.mkExpr(new ProverExpr[] { lFP, rFP });
    }
    private ProverExpr isOVFExp(ProverExpr ee)
    {
        return isOVFExp.mkExpr(new ProverExpr[]{ee});
    }
    private ProverExpr isUDFExp(ProverExpr ee)
    {
        return isUDFExp.mkExpr(new ProverExpr[]{ee});
    }
    private ProverExpr isOVFSigInAdd(ProverExpr em)
    {
        return isOVFSigInAdd.mkExpr(new ProverExpr[]{em});
    }
    private ProverExpr isOVFSigInMul(ProverExpr em)
    {
        return isOVFSigInMul.mkExpr(new ProverExpr[]{em});
    }
    private  ProverExpr extractSigLSBInMul(ProverExpr em)
    {
        return extractSigLSBInMul.mkExpr(new ProverExpr[]{em});
    }
    private  ProverExpr extractSigGInMul(ProverExpr em)
    {
        return extractSigGInMul.mkExpr(new ProverExpr[]{em});
    }
    private  ProverExpr extractSigRInMul(ProverExpr em)
    {
        return extractSigRInMul.mkExpr(new ProverExpr[]{em});
    }
    private  ProverExpr computeStickyInMul(ProverExpr em)
    {
        return computeStickyInMul.mkExpr(new ProverExpr[]{em});
    }
    private ProverExpr requiredRoundingUp(ProverExpr LSB, ProverExpr G, ProverExpr R, ProverExpr S)
    {
        return  requiredRoundingUp.mkExpr(new ProverExpr[]{LSB,G,R,S});
    }
    private ProverExpr roundingUPInMul(ProverExpr FP)
    {
        return  roundingUPInMul.mkExpr(new ProverExpr[]{FP});
    }
    private  ProverExpr makeOVF(ProverExpr sign)
    {
        return makeOVFFun.mkExpr(new ProverExpr[]{sign});
    }
    private ProverExpr makeUDF(ProverExpr sign)
    {
        return makeUDFFun.mkExpr(new ProverExpr[]{sign});
    }
    private ProverExpr existZeroFun(ProverExpr lFP, ProverExpr rFP)
    {
        return existZeroFun.mkExpr(new ProverExpr[]{lFP,rFP});
    }
    private ProverExpr existInfFun(ProverExpr lFP, ProverExpr rFP)
    {
        return existInfFun.mkExpr(new ProverExpr[]{lFP,rFP});
    }
    private ProverExpr existNaNFun(ProverExpr lFP, ProverExpr rFP)
    {
        return existNaNFun.mkExpr(new ProverExpr[]{lFP, rFP});
    }
    private ProverExpr operandsEqInfFun(ProverExpr lFP, ProverExpr rFP)
    {
        return operandsEqInfFun.mkExpr(new ProverExpr[]{lFP, rFP});
    }
    private ProverExpr operandsEqZeroFun(ProverExpr lFP, ProverExpr rFP)
    {
        return operandsEqZeroFun.mkExpr(new ProverExpr[]{lFP, rFP});
    }
    private ProverExpr isNegFun(ProverExpr FP)
    {
        return isNegFun.mkExpr(new ProverExpr[]{FP});
    }
    private ProverExpr areEqSignsFun(ProverExpr lFP, ProverExpr rFP)
    {
        return areEqSignsFun.mkExpr(new ProverExpr[]{lFP, rFP});
    }
    private ProverExpr isInf(ProverExpr FP)
    {
        return isInf.mkExpr(new ProverExpr[]{FP});
    }
    private ProverExpr isNaN(ProverExpr FP)
    {
        return isNaN.mkExpr(new ProverExpr[]{FP});
    }
    private ProverExpr makeNaNFun(ProverExpr FP)
    {
        return  makeNANFun.mkExpr(new ProverExpr[]{FP});
    }
    private ProverExpr makeInfFun(ProverExpr FP)
    {
        return makeInfFun.mkExpr(new ProverExpr[]{FP});
    }
    private  ProverExpr negateFun(ProverExpr FP)
    {
        return negateFun.mkExpr(new ProverExpr[]{FP});
    }
    private ProverExpr existSpecCasInMul(ProverExpr lFP, ProverExpr rFP)
    {
        return existSpecCasInMul.mkExpr(new ProverExpr[]{lFP, rFP});
    }

    public List<ProverHornClause> mkMulDoubleFromExpression2(Expression DoubleExpr, IdentifierExpression idLhs,Expression lhsRefExpr,
                                                            Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom)
    {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof  DoubleLiteral ? ((DoubleLiteral)lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr resultDouble = selectFloatingPoint(result);

        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);

        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr)left;
        ProverTupleExpr tRight = (ProverTupleExpr)right;

        ProverExpr lFP = tLeft.getSubExpr(3);
        ProverExpr rFP = tRight.getSubExpr(3);

        ProverExpr Cond = existNaNFun(lFP,rFP); //existNaN

        ProverExpr idLhsExpr = varMap.get(idLhs.getVariable());
        ProverTupleExpr idLhsTExpr = (ProverTupleExpr)  idLhsExpr;
        ProverExpr mulResult =p.mkTupleUpdate(idLhsTExpr,3,
         p.mkIte(
                 isNaN(rFP),
                 makeNaNFun(lFP),
                lFP
                )
        );
        varMap.put(idLhs.getVariable(),mulResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);
       // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); // postAtom(NaN) <-- existNaN(lFP, rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                existZeroFun(lFP,rFP)
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeNaNFun(lFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
       // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); // postAtom(NaN) <-- existInf(lFP, rFP) & existZero(lFP, rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                p.mkNot(existZeroFun(lFP,rFP)),
                isNegFun(rFP)
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeInfFun(negateFun(lFP)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
       // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); //postAtom(makeInf(negate(lFP))) <-- existInf(lFP, rFP) & !existZero(lFP, rFP) & isNeg(rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                p.mkNot(existZeroFun(lFP,rFP)),
                p.mkNot(isNegFun(rFP))
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeInfFun(lFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
       // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); //postAtom(makeInf(lFP)) <-- existInf(lFP, rFP) & !existZero(lFP, rFP) & !isNeg(rFP)



        Variable resultSignVar = new Variable("resultSignVar", IntType.instance());
        //Variable exponentSub1023Var = new Variable("exponentSub1023Var", Type.instance(), 11);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr leftePlusrighte_Sub_1023 = p.mkBVSub(p.mkBVPlus(p.mkBVZeroExtend(1,leftExponent,11), p.mkBVZeroExtend(1,rightExponent,11), 12),
                p.mkBV(1023, 12), 12);
        ProverExpr leftS_xor_rightS = XORSigns(lFP, rFP);
        varMap.put(resultSignVar, leftS_xor_rightS);
       //varMap.put(exponentSub1023Var, leftePlusrighte_Sub_1023);
        Variable ee = new Variable("ee", Type.instance(), 12);
        varMap.put(ee,leftePlusrighte_Sub_1023);


        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        postPred1Vars.add(resultSignVar);
        postPred1Vars.add(ee);

        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        Cond = p.mkLiteral(true);//p.mkNot(existSpecCasInMul(lFP,rFP)); //!existSpecCase(lFP, rFP)
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond)); // p1(s, ee, lFP, rFP) <-- !existSpecCase(lFP, rFP)

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);

        postAtom1 = postPred1.instPredicate(varMap);

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeOVF(varMap.get(resultSignVar)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isOVFExp(varMap.get(ee));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond)); // postAtom(makeOVF) <-- p1(s, ee, lFP, rFP) & isOVFExp(ee)

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeUDF(varMap.get(resultSignVar)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isUDFExp(varMap.get(ee));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond)); // postAtom(makeUDF) <-- p1(s, ee, lFP, rFP) & isUDFExp(ee)

        Variable extendedFP = new Variable("efp", new WrappedProverType(extendedFloatingPointADT.getType(0)));
        List<Variable> postPred2Vars = new ArrayList<>(postPred1Vars);
        postPred2Vars.remove(resultSignVar);
        postPred2Vars.remove(ee);
        postPred2Vars.add(extendedFP);
        left = expEncoder.exprToProverExpr(DoubleExpr, varMap);

        right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        tLeft = (ProverTupleExpr)left;
        tRight = (ProverTupleExpr)right;

        lFP = tLeft.getSubExpr(3);
        rFP = tRight.getSubExpr(3);
        leftMantisa = floatingPointADT.mkSelExpr(0, 2, lFP);
        rightMantisa = floatingPointADT.mkSelExpr(0, 2, rFP);
        varMap.put(
                extendedFP,
                mkExtendedDoublePE(
                        varMap.get(resultSignVar),//p.mkEq(varMap.get(resultSignVar),p.mkLiteral(0)),
                    varMap.get(ee),
                    p.mkBVMul(
                            p.mkBVZeroExtend(53,leftMantisa,53),
                            p.mkBVZeroExtend(53,rightMantisa,53),106),
                    p.mkLiteral(0),
                    p.mkLiteral(0),
                    p.mkLiteral(0),
                    p.mkLiteral(0)
                )
        );

        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);

        Cond = p.mkAnd(p.mkNot(isOVFExp(varMap.get(ee))),p.mkNot(isUDFExp(varMap.get(ee))));
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond)); // p2(efp) <-- p1(s, ee, lFP, rFP) & !isOVFExp(ee) & !isUDFExp(ee)

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);

        postAtom2 = postPred2.instPredicate(varMap);

        List<Variable> postPred3Vars = new ArrayList<>(postPred2Vars);

        Cond = p.mkNot(isOVFSigInMul(extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        HornPredicate postPred3 = new HornPredicate(p, prePred.name + "_3", postPred3Vars);
        ProverExpr postAtom3 = postPred3.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond)); //p3(efp) <-- p2(efp) & !isOVFSig(m(efp))

        Cond = isOVFSigInMul(extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP)));
        varMap.put(
                extendedFP,
                mkExtendedDoublePE(
                        extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP)),
                        p.mkBVPlus(
                                extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))
                                ,p.mkBV(1,12),
                                12),
                        p.mkBVlshr(
                                extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP)),
                                p.mkBV(1,106),
                                106),
                        extendedFloatingPointADT.mkSelExpr(0,3,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,4,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,5,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,6,varMap.get(extendedFP))
                )
        );

        postAtom3 = postPred3.instPredicate(varMap);


        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond)); //p3(efp(s(efp),e(efp)+1,shr(m(efp),1),isInf(efp), ... )) <-- p2(efp) & isOVFSig(m(efp))

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred3Vars, varMap);

        postAtom3 = postPred3.instPredicate(varMap);

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeOVF(extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP))));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isOVFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond)); // postAtom(makeOVF) <-- p3(efp) & isOVFExp(e(efp))

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeUDF(extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP))));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isUDFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond)); // postAtom(makeUDF) <-- p3(efp) & isUDFExp(e(efp))


        Variable resultFP = new Variable("resultFP", new WrappedProverType(floatingPointADT.getType(0)));
        Variable LSB = new Variable("LSB", Type.instance(),1);
        Variable G = new Variable("G", Type.instance(),1);
        Variable R = new Variable("R", Type.instance(),1);
        Variable S = new Variable("S", Type.instance(),1);
        List<Variable> postPred4Vars = new ArrayList<>(postPred3Vars);
        postPred4Vars.add(resultFP);
        postPred4Vars.add(LSB);
        postPred4Vars.add(G);
        postPred4Vars.add(R);
        postPred4Vars.add(S);
        postPred4Vars.remove(extendedFP);
        varMap.put(
                resultFP,
                mkDoublePE(
                        extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP)),
                        p.mkBVExtract(10,0,
                                extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))),
                        p.mkBVExtract(104,52,
                                extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))),
                        extendedFloatingPointADT.mkSelExpr(0,3,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,4,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,5,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,6,varMap.get(extendedFP))
                )
                );
        varMap.put(LSB, extractSigLSBInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(G, extractSigGInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(R,extractSigRInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(S, computeStickyInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));

        HornPredicate postPred4 = new HornPredicate(p, prePred.name + "_4", postPred4Vars);
        ProverExpr postAtom4 = postPred4.instPredicate(varMap);

        Cond =p.mkAnd(
                p.mkNot(isOVFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)))),
                p.mkNot(isUDFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))))
        );
        clauses.add(p.mkHornClause(postAtom4, new ProverExpr[]{postAtom3}, Cond)); // p4(efp,LSB,G,R,S) <-- p3(efp) & !isOVFExp(e(efp)) & !isUDFExp(e(efp))


        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred4Vars, varMap);

        postAtom4 = postPred4.instPredicate(varMap);

        Cond = p.mkNot(requiredRoundingUp(varMap.get(LSB),varMap.get(G), varMap.get(R), varMap.get(S)));
       // p.mkNot(requiredRoundingUp(p.mkBV(1,1),p.mkBV(0,1),varMap.get(R), varMap.get(S)));//
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, varMap.get(resultFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom4}, Cond));//postAtom(fp) <-- p4(fp, LSB, G, R, S) & !requiredRoundingUp(LSB, G, R, S)


        Cond = requiredRoundingUp(varMap.get(LSB),varMap.get(G), varMap.get(R), varMap.get(S));
        //requiredRoundingUp(p.mkBV(1,1),p.mkBV(0,1),varMap.get(R), varMap.get(S));//

        ProverExpr resFP = varMap.get(resultFP);
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);
        varMap.put(
                extendedFP,
                roundingUPInMul(resFP)
        );
        postAtom2 = postPred2.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom4}, Cond)); //p2(roundUp(fp)) <-- p4(fp, LSB, G, R, S) & requiredRoundingUp(LSB, G, R, S)



        return clauses;
    }
    public List<ProverHornClause>  floatMulFromExp2(Expression FloatExpr, IdentifierExpression idLhs,Expression lhsRefExpr, Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom)
    {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof FloatLiteral ? ((FloatLiteral)lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalFloat = selectFloatingPoint(FloatExpr, varMap);
        if (internalFloat == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalFloat.toString(), lhsRefExprType);
        //ProverExpr resultDouble = selectFloatingPoint(result);

        ProverExpr left = expEncoder.exprToProverExpr(FloatExpr, varMap);

        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr)left;
        ProverTupleExpr tRight = (ProverTupleExpr)right;

        ProverExpr lFP = tLeft.getSubExpr(3);
        ProverExpr rFP = tRight.getSubExpr(3);

        ProverExpr Cond = existNaNFun(lFP,rFP); //existNaN

        ProverExpr idLhsExpr = varMap.get(idLhs.getVariable());
        ProverTupleExpr idLhsTExpr = (ProverTupleExpr)  idLhsExpr;
        ProverExpr mulResult =p.mkTupleUpdate(idLhsTExpr,3,
                p.mkIte(
                        isNaN(rFP),
                        makeNaNFun(lFP),
                        lFP
                )
        );
        varMap.put(idLhs.getVariable(),mulResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);
        // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); // postAtom(NaN) <-- existNaN(lFP, rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                existZeroFun(lFP,rFP)
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeNaNFun(lFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
        // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); // postAtom(NaN) <-- existInf(lFP, rFP) & existZero(lFP, rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                p.mkNot(existZeroFun(lFP,rFP)),
                isNegFun(rFP)
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeInfFun(negateFun(lFP)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
        // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); //postAtom(makeInf(negate(lFP))) <-- existInf(lFP, rFP) & !existZero(lFP, rFP) & isNeg(rFP)

        Cond = p.mkAnd(
                existInfFun(lFP,rFP),
                p.mkNot(existZeroFun(lFP,rFP)),
                p.mkNot(isNegFun(rFP))
        );
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeInfFun(lFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);
        // clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond)); //postAtom(makeInf(lFP)) <-- existInf(lFP, rFP) & !existZero(lFP, rFP) & !isNeg(rFP)



        Variable resultSignVar = new Variable("resultSignVar", IntType.instance());
        //Variable exponentSub1023Var = new Variable("exponentSub1023Var", Type.instance(), 11);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr leftePlusrighte_Sub_127 = p.mkBVSub(p.mkBVPlus(p.mkBVZeroExtend(1,leftExponent,8), p.mkBVZeroExtend(1,rightExponent,8), 9),
                p.mkBV(127, 9), 9);
        ProverExpr leftS_xor_rightS = XORSigns(lFP, rFP);
        varMap.put(resultSignVar, leftS_xor_rightS);
        //varMap.put(exponentSub1023Var, leftePlusrighte_Sub_1023);
        Variable ee = new Variable("ee", Type.instance(), 9);
        varMap.put(ee,leftePlusrighte_Sub_127);


        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        postPred1Vars.add(resultSignVar);
        postPred1Vars.add(ee);

        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        Cond = p.mkLiteral(true);//p.mkNot(existSpecCasInMul(lFP,rFP)); //!existSpecCase(lFP, rFP)
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond)); // p1(s, ee, lFP, rFP) <-- !existSpecCase(lFP, rFP)

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);

        postAtom1 = postPred1.instPredicate(varMap);

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeOVF(varMap.get(resultSignVar)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isOVFExp(varMap.get(ee));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond)); // postAtom(makeOVF) <-- p1(s, ee, lFP, rFP) & isOVFExp(ee)

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeUDF(varMap.get(resultSignVar)));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isUDFExp(varMap.get(ee));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond)); // postAtom(makeUDF) <-- p1(s, ee, lFP, rFP) & isUDFExp(ee)

        Variable extendedFP = new Variable("efp", new WrappedProverType(extendedFloatingPointADT.getType(0)));
        List<Variable> postPred2Vars = new ArrayList<>(postPred1Vars);
        postPred2Vars.remove(resultSignVar);
        postPred2Vars.remove(ee);
        postPred2Vars.add(extendedFP);
        left = expEncoder.exprToProverExpr(FloatExpr, varMap);

        right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        tLeft = (ProverTupleExpr)left;
        tRight = (ProverTupleExpr)right;

        lFP = tLeft.getSubExpr(3);
        rFP = tRight.getSubExpr(3);
        leftMantisa = floatingPointADT.mkSelExpr(0, 2, lFP);
        rightMantisa = floatingPointADT.mkSelExpr(0, 2, rFP);
        varMap.put(
                extendedFP,
                mkExtendedDoublePE(
                        varMap.get(resultSignVar),//p.mkEq(varMap.get(resultSignVar),p.mkLiteral(0)),
                        varMap.get(ee),
                        p.mkBVMul(
                                p.mkBVZeroExtend(24,leftMantisa,24),
                                p.mkBVZeroExtend(24,rightMantisa,24),48),
                        p.mkLiteral(0),
                        p.mkLiteral(0),
                        p.mkLiteral(0),
                        p.mkLiteral(0)
                )
        );

        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);

        Cond = p.mkAnd(p.mkNot(isOVFExp(varMap.get(ee))),p.mkNot(isUDFExp(varMap.get(ee))));
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond)); // p2(efp) <-- p1(s, ee, lFP, rFP) & !isOVFExp(ee) & !isUDFExp(ee)

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);

        postAtom2 = postPred2.instPredicate(varMap);

        List<Variable> postPred3Vars = new ArrayList<>(postPred2Vars);

        Cond = p.mkNot(isOVFSigInMul(extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        HornPredicate postPred3 = new HornPredicate(p, prePred.name + "_3", postPred3Vars);
        ProverExpr postAtom3 = postPred3.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond)); //p3(efp) <-- p2(efp) & !isOVFSig(m(efp))

        Cond = isOVFSigInMul(extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP)));
        varMap.put(
                extendedFP,
                mkExtendedDoublePE(
                        extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP)),
                        p.mkBVPlus(
                                extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))
                                ,p.mkBV(1,9),
                                9),
                        p.mkBVlshr(
                                extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP)),
                                p.mkBV(1,48),
                                48),
                        extendedFloatingPointADT.mkSelExpr(0,3,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,4,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,5,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,6,varMap.get(extendedFP))
                )
        );

        postAtom3 = postPred3.instPredicate(varMap);


        clauses.add(p.mkHornClause(postAtom3, new ProverExpr[]{postAtom2}, Cond)); //p3(efp(s(efp),e(efp)+1,shr(m(efp),1),isInf(efp), ... )) <-- p2(efp) & isOVFSig(m(efp))

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred3Vars, varMap);

        postAtom3 = postPred3.instPredicate(varMap);

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeOVF(extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP))));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isOVFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond)); // postAtom(makeOVF) <-- p3(efp) & isOVFExp(e(efp))

        mulResult =p.mkTupleUpdate(idLhsTExpr,3, makeUDF(extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP))));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        Cond = isUDFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom3}, Cond)); // postAtom(makeUDF) <-- p3(efp) & isUDFExp(e(efp))


        Variable resultFP = new Variable("resultFP", new WrappedProverType(floatingPointADT.getType(0)));
        Variable LSB = new Variable("LSB", Type.instance(),1);
        Variable G = new Variable("G", Type.instance(),1);
        Variable R = new Variable("R", Type.instance(),1);
        Variable S = new Variable("S", Type.instance(),1);
        List<Variable> postPred4Vars = new ArrayList<>(postPred3Vars);
        postPred4Vars.add(resultFP);
        postPred4Vars.add(LSB);
        postPred4Vars.add(G);
        postPred4Vars.add(R);
        postPred4Vars.add(S);
        postPred4Vars.remove(extendedFP);
        varMap.put(
                resultFP,
                mkDoublePE(
                        extendedFloatingPointADT.mkSelExpr(0,0,varMap.get(extendedFP)),
                        p.mkBVExtract(7,0,
                                extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))),
                        p.mkBVExtract(46,23,
                                extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))),
                        extendedFloatingPointADT.mkSelExpr(0,3,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,4,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,5,varMap.get(extendedFP)),
                        extendedFloatingPointADT.mkSelExpr(0,6,varMap.get(extendedFP))
                )
        );
        varMap.put(LSB, extractSigLSBInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(G, extractSigGInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(R,extractSigRInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));
        varMap.put(S, computeStickyInMul( extendedFloatingPointADT.mkSelExpr(0,2,varMap.get(extendedFP))));

        HornPredicate postPred4 = new HornPredicate(p, prePred.name + "_4", postPred4Vars);
        ProverExpr postAtom4 = postPred4.instPredicate(varMap);

        Cond = p.mkAnd(
                p.mkNot(isOVFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP)))),
                p.mkNot(isUDFExp(extendedFloatingPointADT.mkSelExpr(0,1,varMap.get(extendedFP))))
        );
        clauses.add(p.mkHornClause(postAtom4, new ProverExpr[]{postAtom3}, Cond)); // p4(efp,LSB,G,R,S) <-- p3(efp) & !isOVFExp(e(efp)) & !isUDFExp(e(efp))


        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred4Vars, varMap);

        postAtom4 = postPred4.instPredicate(varMap);

        Cond = p.mkNot(requiredRoundingUp(varMap.get(LSB),varMap.get(G), varMap.get(R), varMap.get(S)));
        //p.mkNot(requiredRoundingUp(p.mkBV(0,1),p.mkBV(1,1),p.mkBV(1,1), varMap.get(S)));//
        mulResult =p.mkTupleUpdate(idLhsTExpr,3, varMap.get(resultFP));
        varMap.put(idLhs.getVariable(),mulResult);
        postAtom = postPred.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom4}, Cond));//postAtom(fp) <-- p4(fp, LSB, G, R, S) & !requiredRoundingUp(LSB, G, R, S)


        Cond = requiredRoundingUp(varMap.get(LSB),varMap.get(G), varMap.get(R), varMap.get(S));
        //requiredRoundingUp(p.mkBV(0,1),p.mkBV(1,1),p.mkBV(1,1), varMap.get(S));//

        ProverExpr resFP = varMap.get(resultFP);
        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);
        varMap.put(
                extendedFP,
                roundingUPInMul(resFP)
        );
        postAtom2 = postPred2.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom4}, Cond)); //p2(roundUp(fp)) <-- p4(fp, LSB, G, R, S) & requiredRoundingUp(LSB, G, R, S)



        return clauses;
    }

    public ProverExpr findOrCreateProverBVVar(Variable v, int bitLen, Map<Variable, ProverExpr> varMap) {
        if (!varMap.containsKey(v)) {
            varMap.put(v, createBVVariable(v,bitLen));
        }
        return varMap.get(v);
    }
    public ProverExpr createBVVariable(Variable v,int bitLen) {

        return  BvHornVar(v.getName() + "_" +  HornHelper.hh().newVarNum(), bitLen);
    }
    private ProverExpr mkNotNullConstraint(ProverExpr refPE) {
        return p.mkNot(p.mkEq(p.mkTupleSelect(refPE, 0), lit(0)));
    }
    private ProverExpr lit(int value) {
        return p.mkLiteral(value);
    }
    private ProverExpr mkRefHornVariable(String name, ReferenceType refType) {
        ProverType proverType = HornHelper.hh().getProverType(p, refType);
//        if (name == null) {
//            int id = HornHelper.hh().newVarNum();
//            name = String.format(STRING_REF_TEMPLATE, id);
//        }
        return p.mkHornVariable(name, proverType);
    }
    private ProverExpr BvHornVar(String name,int bitLength) {
        return p.mkHornVariable(name, p.getBVType(bitLength));
    }
    private ProverExpr selectFloatingPoint(Expression expr, Map<Variable, ProverExpr> varMap) {
        if (expr instanceof DoubleLiteral) {
            return mkDoublePE(((DoubleLiteral) expr).getValue());
        }
        else if (expr instanceof FloatLiteral) {
            return mkFloatPE(((FloatLiteral) expr).getValue());
        }
        else if (expr instanceof IdentifierExpression) {
            ProverExpr pe = proverExprFromIdExpr((IdentifierExpression) expr, varMap);
            Verify.verify(pe != null, "cannot extract Double from " + expr);
            return selectFloatingPoint(pe);
        } else {
            Verify.verify(false, "cannot extract Duble from " + expr);
            throw new RuntimeException();
        }
    }
    public static ProverExpr proverExprFromIdExpr(IdentifierExpression ie, Map<Variable, ProverExpr> varMap) {
        return varMap.get(ie.getVariable());
    }
    private ProverExpr selectFloatingPoint(ProverExpr pe) {
        if (pe instanceof ProverTupleExpr) {
            return p.mkTupleSelect(pe, 3);
        } else {
            return pe;
        }
    }

    public FloatingPointEncoder(Prover p,
                                ProverADT floatingPointADT,
                                ProverADT tempFloatingPointADT,
                                ProverADT tempFloatingPointOperandsADT,
                                Precision precision,
                                ProverFun xORSigns,
                                ProverFun isOVFExp,
                                ProverFun isUDFExp,
                                ProverFun isOVFSigInAdd,
                                ProverFun isOVFSigInMul,
                                ProverFun extractSigLSBInMul,
                                ProverFun extractSigGInMul,
                                ProverFun extractSigRInMul,
                                ProverFun computeStickyInMul,
                                ProverFun requiredRoundingUp,
                                ProverFun roundingUPInMul,
                                ProverFun makeOVFFun,
                                ProverFun makeUDFFun,
                                ProverFun existZeroFun,
                                ProverFun existInfFun,
                                ProverFun existNaNFun,
                                ProverFun operandsEqInfFun,
                                ProverFun operandsEqZeroFun,
                                ProverFun isNegFun,
                                ProverFun areEqSignsFun,
                                ProverFun isInf,
                                ProverFun isNaN,
                                ProverFun makeNANFun,
                                ProverFun makeInfFun,
                                ProverFun negateFun,
                                ProverFun existSpecCasInMul
                                )
    {
        this.p = p;
        this.floatingPointADT = floatingPointADT;
        this.extendedFloatingPointADT = tempFloatingPointADT;
        this.tempFloatingPointOperandsADT = tempFloatingPointOperandsADT;
        this.floatingPointPrecision = precision;
        this.xORSigns = xORSigns;
        this.isOVFExp = isOVFExp;
        this.isUDFExp = isUDFExp;
        this.isOVFSigInAdd = isOVFSigInAdd;
        this.isOVFSigInMul = isOVFSigInMul;
        this.extractSigLSBInMul = extractSigLSBInMul;
        this.extractSigGInMul = extractSigGInMul;
        this.extractSigRInMul = extractSigRInMul;
        this.computeStickyInMul = computeStickyInMul;
        this.requiredRoundingUp = requiredRoundingUp;
        this.roundingUPInMul = roundingUPInMul;
        this.makeOVFFun = makeOVFFun;
        this.makeUDFFun = makeUDFFun;
        this.existZeroFun = existZeroFun;
        this.existInfFun = existInfFun;
        this.existNaNFun = existNaNFun;
        this.operandsEqZeroFun = operandsEqZeroFun;
        this.operandsEqInfFun = operandsEqInfFun;
        this.isNegFun = isNegFun;
        this.areEqSignsFun = areEqSignsFun;
        this.isInf = isInf;
        this.isNaN = isNaN;
        this.makeNANFun = makeNANFun;
        this.makeInfFun = makeInfFun;
        this.negateFun = negateFun;
        this.existSpecCasInMul = existSpecCasInMul;
        e = (precision == Precision.Single ? 8 : 11);
        f = (precision == Precision.Single ? 24 : 53);
    }
    public ProverExpr mkDoublePE(@Nullable Double value) {
        if( value != null)
            return mkDoublePEFromValue(value, floatingPointADT);

        return new ProverExpr() {
            @Override
            public ProverType getType() {
                return null;
            }

            @Override
            public BigInteger getIntLiteralValue() {
                return null;
            }

            @Override
            public boolean getBooleanLiteralValue() {
                return false;
            }
        };
    }
    public ProverExpr mkFloatPE(@Nullable Float value) {
        if( value != null)
            return mkFloatPEFromValue(value, floatingPointADT);

        return new ProverExpr() {
            @Override
            public ProverType getType() {
                return null;
            }

            @Override
            public BigInteger getIntLiteralValue() {
                return null;
            }

            @Override
            public boolean getBooleanLiteralValue() {
                return false;
            }
        };
    }
    public ProverExpr mkExtendedDoublePE(ProverExpr DoublePE)
    {
        ProverExpr sign = floatingPointADT.mkSelExpr(0, 0, DoublePE);
        ProverExpr exponent = floatingPointADT.mkSelExpr(0, 1, DoublePE);
        ProverExpr mantissa = p.mkBVZeroExtend(2,floatingPointADT.mkSelExpr(0, 2, DoublePE),55);
        ProverExpr isNaN = floatingPointADT.mkSelExpr(0, 3, DoublePE);
        ProverExpr isInf = floatingPointADT.mkSelExpr(0, 4, DoublePE);
        ProverExpr OVF = floatingPointADT.mkSelExpr(0, 5, DoublePE);
        ProverExpr UDF = floatingPointADT.mkSelExpr(0, 6, DoublePE);
        return mkExtendedDoublePE(sign, exponent, mantissa, isNaN, isInf,OVF,UDF);
    }
    private ProverExpr mkExtendedDoublePE(ProverExpr sign, ProverExpr exponent,ProverExpr mantissa, ProverExpr isNan, ProverExpr isInf,ProverExpr OVF, ProverExpr UDF)
    {
        return extendedFloatingPointADT.mkCtorExpr(0, new ProverExpr[]{sign, exponent, mantissa, isNan, isInf, OVF, UDF});
    }
    public ProverExpr mkTempDoubleOperandsPE(ProverExpr tempFloatingPointADTLeft, ProverExpr tempFloatingPointADTRight) {

            return mkTempDoublePEFromOperands(tempFloatingPointADTLeft, tempFloatingPointADTRight);
    }
    private ProverExpr mkTempDoublePEFromOperands(ProverExpr tempFloatingPointADTLeft, ProverExpr tempFloatingPointADTRight)
    {
        ProverExpr resultPE = tempFloatingPointOperandsADT.mkCtorExpr(0, new ProverExpr[]{tempFloatingPointADTLeft, tempFloatingPointADTRight});

        return resultPE;
    }

    private ProverExpr BVLit(BigInteger value, int bitLength)
    {
        return  p.mkBVLiteral(value, bitLength);
    }
    private ProverExpr SignedBVLit(ProverExpr expr, int bitLength)
    {
        return  p.mkSignedBVLiteral(expr, bitLength);
    }
    private ProverExpr mkDoublePEFromValue(double value, ProverADT floatingPointADT)
    {
        ProverExpr sign, exponent,mantissa, isNan,isInf, OVF, UDF;

        IeeeFloatt ieeeOne = new IeeeFloatt(new IeeeFloatSpect(f-1, e));
        ieeeOne.fromDouble(value);

        sign = p.mkLiteral(!ieeeOne.get_sign()  ? 0 : 1);//BVLit( new BigInteger(ieeeOne.get_sign() ? "1" : "0"),1);
        exponent = value > 0 ? BVLit(ieeeOne.get_exponent().add(ieeeOne.getSpec().maxExponent()),e) : BVLit(ieeeOne.get_exponent().add(ieeeOne.getSpec().maxExponent()).subtract(BigInteger.ONE),e);
        isNan = p.mkLiteral(ieeeOne.NaN_flag == null || !ieeeOne.NaN_flag ? 0 : 1);
        isInf = p.mkLiteral(ieeeOne.infinity_flag == null || !ieeeOne.infinity_flag  ? 0 : 1);

        OVF = p.mkLiteral(0);
        UDF = p.mkLiteral(0);
       //ieeeOne.get_exponent().doubleValue()
       // byte [] ex = ieeeOne.get_exponent().toByteArray();
       // byte [] ma = ieeeOne.get_fraction().toByteArray();
        mantissa = BVLit(ieeeOne.get_fraction(),f);
       //ieeeOne.get_fraction().add(BigInteger.ONE).doubleValue()
        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa,isNan,isInf, OVF, UDF });

        return  res;
    }
    private ProverExpr mkFloatPEFromValue(float value, ProverADT floatingPointADT)
    {
        ProverExpr sign, exponent,mantissa, isNan,isInf, OVF, UDF;

        IeeeFloatt ieeeOne = new IeeeFloatt(new IeeeFloatSpect(f-1, e));
        ieeeOne.fromFloat(value);

        sign = p.mkLiteral(!ieeeOne.get_sign()  ? 0 : 1);//BVLit( new BigInteger(ieeeOne.get_sign() ? "1" : "0"),1);
        exponent = value > 0 ? BVLit(ieeeOne.get_exponent().add(ieeeOne.getSpec().maxExponent()),e) : BVLit(ieeeOne.get_exponent().add(ieeeOne.getSpec().maxExponent()).subtract(BigInteger.ONE),e);
        isNan = p.mkLiteral(ieeeOne.NaN_flag == null || !ieeeOne.NaN_flag ? 0 : 1);
        isInf = p.mkLiteral(ieeeOne.infinity_flag == null || !ieeeOne.infinity_flag  ? 0 : 1);

        OVF = p.mkLiteral(0);
        UDF = p.mkLiteral(0);
        //ieeeOne.get_exponent().doubleValue()
        // byte [] ex = ieeeOne.get_exponent().toByteArray();
        // byte [] ma = ieeeOne.get_fraction().toByteArray();
        mantissa = BVLit(ieeeOne.get_fraction(),f);
        //ieeeOne.get_fraction().add(BigInteger.ONE).doubleValue()
        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa,isNan,isInf, OVF, UDF });

        return  res;
    }
    public ProverExpr mkDoublePE( ProverExpr sign, ProverExpr exponent,ProverExpr mantissa, ProverExpr isNan, ProverExpr isInf,ProverExpr OVF, ProverExpr UDF)
    {


        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa,isNan,isInf,OVF, UDF });

        return  res;
    }
}
