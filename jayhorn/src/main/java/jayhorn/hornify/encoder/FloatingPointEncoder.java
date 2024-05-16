package jayhorn.hornify.encoder;

import com.google.common.base.Verify;

import jayhorn.hornify.HornHelper;
import jayhorn.hornify.HornPredicate;
import jayhorn.solver.*;
import jayhorn.solver.princess.PrincessFloatingPointADTFactory;
import jayhorn.solver.princess.PrincessFloatingPointType;
import scala.Int;
import soottocfg.cfg.expression.BinaryExpression;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.expression.IteExpression;
import soottocfg.cfg.expression.literal.DoubleLiteral;
import soottocfg.cfg.expression.literal.StringLiteral;
import soottocfg.cfg.type.BoolType;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.type.ReferenceType;
import soottocfg.cfg.type.Type;
import soottocfg.cfg.variable.Variable;

import javax.annotation.Nullable;
import java.awt.datatransfer.FlavorListener;
import java.math.BigInteger;
import java.util.*;

public class FloatingPointEncoder {

    private  ExpressionEncoder expEncoder;

    public enum Precision{
        Single,
        Double
    }
    private Prover p;
    private ProverADT floatingPointADT;

    private Precision floatingPointPrecision;

    public ProverADT getFloatingPointADT() {
        return floatingPointADT;
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
    public List<ProverHornClause> handleFloatingPointExpr(Expression e, IdentifierExpression idLhs,Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom ,ExpressionEncoder expEnc) {
        expEncoder = expEnc;
        if (e instanceof BinaryExpression) {
            final BinaryExpression be = (BinaryExpression) e;
            Expression leftExpr = be.getLeft();
            Expression rightExpr = be.getRight();
            switch (be.getOp()) {
                case ToDouble:
                case ToFloat:
                    return mkToDoubleFromExpression(leftExpr, idLhs,rightExpr,varMap, postPred, prePred, preAtom);
                case AssumeDouble:
                    return mkAssumeDoubleFromExpression(rightExpr,varMap, postPred, prePred, preAtom);
                case AssumeFloat:
                    return mkAssumeFloatFromExpression(rightExpr,varMap, postPred, prePred, preAtom);
                case MulDouble:
                    return mkMulDoubleFromExpression(leftExpr, idLhs,rightExpr,varMap, postPred, prePred, preAtom);
                case AddDouble:
                    return mkAddDoubleFromExpression(leftExpr, idLhs,rightExpr,varMap, postPred, prePred, preAtom);

                default: return null;

            }
        }
        else if(e instanceof IteExpression)
        {
            final IteExpression ie = (IteExpression) e;

            final BinaryExpression condExpr = (BinaryExpression) ie.getCondition();
            final BinaryExpression be = (BinaryExpression) condExpr;
            Expression leftExpr = be.getLeft();
            Expression rightExpr = be.getRight();
            final ProverExpr thenExpr = expEncoder.exprToProverExpr(ie.getThenExpr(), varMap);
            final ProverExpr elseExpr = expEncoder.exprToProverExpr(ie.getElseExpr(), varMap);
            //ProverExpr finalExpr = p.mkIte(condExpr, thenExpr, elseExpr);
            switch (be.getOp()) {
                case LeDouble:
                    return mkLeDoubleFromExpression(leftExpr, idLhs,rightExpr,varMap, postPred, prePred, preAtom,thenExpr,elseExpr);
                default: return null;
            }
        }
        return null;
    }
    public List<ProverHornClause> mkAssumeDoubleFromExpression(Expression rightExpr, Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom)
    {
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
    public List<ProverHornClause> mkToDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs,Expression lhsRefExpr,
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

    public List<ProverHornClause> mkLeDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs,Expression lhsRefExpr,
                                                            Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom, ProverExpr thenExpr, ProverExpr elseExpr)
    {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof  DoubleLiteral ? ((DoubleLiteral)lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr)left;
        ProverTupleExpr tRight = (ProverTupleExpr)right;

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

        HornPredicate postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        ProverExpr Cond = p.mkNot(p.mkEq(((ProverTupleExpr) left).getSubExpr(3),((ProverTupleExpr) right).getSubExpr(3)));
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));
        //-----------------------------------------------------------------------------------------------------


        List<Variable> postPred2Vars = new ArrayList<>(prePred.variables);
        HornPredicate postPred2 =  new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);
        Cond = p.mkEq(leftSign,rightSign);
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, Cond));
        //-----------------------------------------------------------------------------------------------------

        varMap.put(idLhs.getVariable(),p.mkIte(p.mkBVUgt(leftSign,rightSign),thenExpr,elseExpr));
        ProverExpr postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftSign,rightSign));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom1}, Cond));

        varMap.put(idLhs.getVariable(),p.mkIte(p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUgt(leftMantisa,rightMantisa),p.mkBVUlt(leftMantisa,rightMantisa)),thenExpr,elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(leftExponent,rightExponent);
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.replace(idLhs.getVariable(),varMap.get(idLhs.getVariable()),p.mkIte(p.mkIte(p.mkEq(leftSign,p.mkBV(1,1)),p.mkBVUgt(leftExponent,rightExponent),p.mkBVUlt(leftExponent,rightExponent)),thenExpr,elseExpr));
        postAtom = postPred.instPredicate(varMap);
        Cond = p.mkNot(p.mkEq(leftExponent,rightExponent));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{postAtom2}, Cond));

        varMap.put(idLhs.getVariable(),thenExpr);
         postAtom = postPred.instPredicate(varMap);
        Cond = p.mkEq(((ProverTupleExpr) left).getSubExpr(3),((ProverTupleExpr) right).getSubExpr(3));
        clauses.add(p.mkHornClause(postAtom, new ProverExpr[]{preAtom}, Cond));

        return clauses;
    }
    public List<ProverHornClause> mkAddDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs,Expression lhsRefExpr,
                                                            Map<Variable, ProverExpr> varMap, HornPredicate postPred, HornPredicate prePred, ProverExpr preAtom)
    {
        List<ProverHornClause> clauses = new LinkedList<ProverHornClause>();
        ReferenceType lhsRefExprType = (ReferenceType) (lhsRefExpr instanceof  DoubleLiteral ? ((DoubleLiteral)lhsRefExpr).getVariable().getType() : lhsRefExpr.getType());

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr left = expEncoder.exprToProverExpr(DoubleExpr, varMap);
        ProverExpr right = expEncoder.exprToProverExpr(lhsRefExpr, varMap);
        ProverTupleExpr tLeft = (ProverTupleExpr)left;
        ProverTupleExpr tRight = (ProverTupleExpr)right;

       // final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));// FloatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr ZeroExtendedLeftM = p.mkBVZeroExtend(1,leftMantisa,53);
        ProverExpr ZeroExtendedRightM = p.mkBVZeroExtend(1,rightMantisa,53);
        ProverExpr eLeft_eRight_diff = p.mkBVZeroExtend(43,p.mkBVSub(leftExponent,rightExponent,11),11);
        ProverExpr eRight_eLeft_diff = p.mkBVZeroExtend(43,p.mkBVSub(rightExponent,leftExponent,11),11);
        ProverExpr RightShiftedRightM =  p.mkBVlshr(ZeroExtendedRightM,eLeft_eRight_diff,54);
        ProverExpr RightShiftedleftM =  p.mkBVlshr(ZeroExtendedLeftM,eRight_eLeft_diff,54);

        Variable resultSignVar = new Variable("resultSignVar", Type.instance(),1);
        Variable resultExponentVar = new Variable("resultExponentVar",  Type.instance(),11);
        Variable leftMantissaVar = new Variable("leftMantissaVar", Type.instance(),54);
        Variable rightMantissaVar = new Variable("rightMantissaVar",  Type.instance(),54);



        List<Variable> postPred1Vars = new ArrayList<>(prePred.variables);
        postPred1Vars.add(resultSignVar);
        postPred1Vars.add(resultExponentVar);
        postPred1Vars.add(leftMantissaVar);
        postPred1Vars.add(rightMantissaVar);

        //varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred1 = new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        varMap.put(resultSignVar,leftSign);
        varMap.put(resultExponentVar,leftExponent/*p.mkBV(1019,11)*/);
        varMap.put(leftMantissaVar,ZeroExtendedLeftM);
        varMap.put(rightMantissaVar,RightShiftedRightM);
        //HornPredicate postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);

        ProverExpr postAtom1 = postPred1.instPredicate(varMap);
        ProverExpr Cond = p.mkBVUge(leftExponent,rightExponent);/*p.mkLiteral(true)*/;
        clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, Cond));
        //----------------------------------------------------------------------------
        varMap.replace(resultExponentVar,varMap.get(resultExponentVar), rightExponent);
        varMap.replace(leftMantissaVar, varMap.get(leftMantissaVar),RightShiftedleftM);
        varMap.replace(rightMantissaVar,varMap.get(rightMantissaVar),ZeroExtendedRightM);

        HornHelper.hh().findOrCreateProverVar(p, postPred1Vars, varMap);
        HornPredicate postPred2 = new HornPredicate(p, prePred.name + "_2", postPred1Vars);
        //postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);
         Cond = p.mkBVUlt(leftExponent,rightExponent);
        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{preAtom}, Cond));

        //--------------------------------------------------------------------------

        varMap = new HashMap<Variable, ProverExpr>();
        // First create the atom for prePred.
        HornHelper.hh().findOrCreateProverVar(p, postPred1.variables, varMap);
        postAtom1 = postPred1.instPredicate(varMap);


        List<Variable> postPred2Vars = new ArrayList<>(postPred1Vars) ;
        Variable leadingZeroCountVar = new Variable("leadingZeroCountVar", Type.instance(), 53);
        Variable mantissaAddResVar = new Variable("mantissaAddResVar", Type.instance(),54);
        postPred2Vars.remove(leftMantissaVar);
        postPred2Vars.remove(rightMantissaVar);
        postPred2Vars.add(mantissaAddResVar);
        postPred2Vars.add(leadingZeroCountVar);

        ProverExpr MantissaAdition =p.mkBVPlus(varMap.get(leftMantissaVar),varMap.get(rightMantissaVar),54);/* p.mkBV(new BigInteger("10808639105689191"),54);*/
        varMap.put(leadingZeroCountVar, p.mkBV(0,53));
        varMap.put(mantissaAddResVar,MantissaAdition );
        HornHelper.hh().findOrCreateProverVar(p, postPred2Vars, varMap);


        HornPredicate postPred3 =  new HornPredicate(p, prePred.name + "_3", postPred2Vars);
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
        Cond = p.mkEq(p.mkBVExtract(53,53,varMap.get(mantissaAddResVar)),p.mkBV(0,1));
        postAtom3 = postPred3.instPredicate(varMap);

        varMap.replace(leadingZeroCountVar, varMap.get(leadingZeroCountVar), p.mkBVPlus(varMap.get(leadingZeroCountVar),p.mkBV(1,53),53));
        varMap.replace(mantissaAddResVar, varMap.get(mantissaAddResVar),p.mkBVshl(varMap.get(mantissaAddResVar),p.mkBV(1,54),54));
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
        ProverTupleExpr idLhsTExpr = (ProverTupleExpr)  idLhsExpr;
        ProverExpr addResult = p.mkTupleUpdate(idLhsTExpr,3,mkDoublePE(varMap.get(resultSignVar),
                p.mkIte(p.mkEq(varMap.get(leadingZeroCountVar),p.mkBV(0,53)),

                       p.mkBVPlus(varMap.get(resultExponentVar),p.mkBV(1,11),11),
                       p.mkBVPlus( varMap.get(resultExponentVar), p.mkBVExtract(10,0, varMap.get(leadingZeroCountVar)),11)

                ),
                p.mkBVPlus(p.mkBVExtract(53,1,varMap.get(mantissaAddResVar)),p.mkBVZeroExtend(52,p.mkBVExtract(0,0,varMap.get(mantissaAddResVar)),1),53)
        ));
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult,0,tLeft.getSubExpr(0));
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult,1,tLeft.getSubExpr(1));
        addResult = p.mkTupleUpdate((ProverTupleExpr) addResult,2,tLeft.getSubExpr(2));
        varMap.put(idLhs.getVariable(),addResult);
        ProverExpr postAtom = postPred.instPredicate(varMap);

        Cond = p.mkEq(p.mkBVExtract(53,53,varMap.get(mantissaAddResVar)),p.mkBV(1,1));
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

        return  clauses;
    }

    public List<ProverHornClause> mkMulDoubleFromExpression(Expression DoubleExpr, IdentifierExpression idLhs,Expression lhsRefExpr,
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
//floatingPointADT
        //final ProverADT FloatingPointADT = (new PrincessFloatingPointADTFactory()).spawnFloatingPointADT(PrincessFloatingPointType.Precision.Double);
        ProverExpr leftSign = floatingPointADT.mkSelExpr(0, 0, tLeft.getSubExpr(3));
        ProverExpr leftExponent = floatingPointADT.mkSelExpr(0, 1, tLeft.getSubExpr(3));
        ProverExpr leftMantisa = floatingPointADT.mkSelExpr(0, 2, tLeft.getSubExpr(3));
        ProverExpr rightSign = floatingPointADT.mkSelExpr(0, 0, tRight.getSubExpr(3));
        ProverExpr rightExponent = floatingPointADT.mkSelExpr(0, 1, tRight.getSubExpr(3));
        ProverExpr rightMantisa = floatingPointADT.mkSelExpr(0, 2, tRight.getSubExpr(3));

        ProverExpr leftS_xor_rightS = p.mkBVXOR(leftSign, rightSign, 1);
        ProverExpr ZeroExtendedLeftM = p.mkBVZeroExtend(53,leftMantisa,106);
        ProverExpr ZeroExtendedRightM = p.mkBVZeroExtend(53,rightMantisa,106);
        ProverExpr leftePlusrighte_Sub_1023 =  p.mkBVSub(p.mkBVPlus(leftExponent, rightExponent, 11),
                p.mkBV(1023, 11), 11);
        ProverExpr leftM_Mul_rightM = p.mkBVExtract(105,51,p.mkBVMul(ZeroExtendedLeftM, ZeroExtendedRightM, 106));


        Variable resultSignVar = new Variable("resultSignVar", Type.instance(),1);
        Variable exponentSub1023Var = new Variable("exponentSub1023Var", Type.instance(),11);

        Variable mantissaMulResVar = new Variable("mantissaMulResVar", Type.instance(),55);

        varMap.put(resultSignVar,leftS_xor_rightS);
        varMap.put(exponentSub1023Var,leftePlusrighte_Sub_1023);
        varMap.put(mantissaMulResVar,leftM_Mul_rightM);

       List<Variable> postPred1Vars = prePred.variables;
       postPred1Vars.add(resultSignVar);
       postPred1Vars.add(exponentSub1023Var);
       postPred1Vars.add(mantissaMulResVar);


       HornPredicate postPred1 =  new HornPredicate(p, prePred.name + "_1", postPred1Vars);
       ProverExpr postAtom1 = postPred1.instPredicate(varMap);

       clauses.add(p.mkHornClause(postAtom1, new ProverExpr[]{preAtom}, p.mkLiteral(true)));

       //----------------------------------------------------------------------------------------
        varMap.replace(resultSignVar,varMap.get(resultSignVar), createBVVariable(resultSignVar,1));
        varMap.replace(exponentSub1023Var,varMap.get(exponentSub1023Var), createBVVariable(exponentSub1023Var,11));
        varMap.replace(mantissaMulResVar,varMap.get(mantissaMulResVar), createBVVariable(mantissaMulResVar,55));
        postAtom1 = postPred1.instPredicate(varMap);

        Variable mul_0 = new Variable("mul_0", Type.instance(),1);
        Variable mul_1 = new Variable("mul_1", Type.instance(),1);
        Variable mul_54 = new Variable("mul_54", Type.instance(),1);
        Variable mul_53_1 = new Variable("mul_53_1", Type.instance(),53);
        Variable mul_54_2 = new Variable("mul_54_2", Type.instance(),53);
        ProverExpr extract_0_fromMul = p.mkBVExtract(0,0,varMap.get(mantissaMulResVar));
        ProverExpr extract_1_fromMul = p.mkBVExtract(1,1,varMap.get(mantissaMulResVar));
        ProverExpr extract_54_fromMul = p.mkBVExtract(54,54,varMap.get(mantissaMulResVar));
        ProverExpr extract_53_1_fromMul = p.mkBVExtract(53,1,varMap.get(mantissaMulResVar));
        ProverExpr extract_54_2_fromMul = p.mkBVExtract(54,2,varMap.get(mantissaMulResVar));
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
        HornPredicate postPred2 =  new HornPredicate(p, prePred.name + "_2", postPred2Vars);
        ProverExpr postAtom2 = postPred2.instPredicate(varMap);

        clauses.add(p.mkHornClause(postAtom2, new ProverExpr[]{postAtom1}, p.mkLiteral(true)));

        //----------------------------------------------------------------------------------------
        varMap.replace(mul_0,varMap.get(mul_0), createBVVariable(mul_0,1));
        varMap.replace(mul_1,varMap.get(mul_1), createBVVariable(mul_1,1));
        varMap.replace(mul_54,varMap.get(mul_54), createBVVariable(mul_54,1));
        varMap.replace(mul_53_1,varMap.get(mul_53_1), createBVVariable(mul_53_1,53));
        varMap.replace(mul_54_2,varMap.get(mul_54_2), createBVVariable(mul_54_2,53));
        postAtom2 = postPred2.instPredicate(varMap);


        ProverExpr Cond = p.mkEq(varMap.get(mul_54),p.mkBV(1,1));

        ProverExpr mulResult = p.mkTuple(new ProverExpr[]{tLeft.getSubExpr(0), tLeft.getSubExpr(1), tLeft.getSubExpr(2)
                , mkDoublePE(
                        varMap.get(resultSignVar), //sign
                       p.mkBVPlus(varMap.get(exponentSub1023Var),p.mkBV(1,11),11), //exponnet
                       p.mkBVPlus(varMap.get(mul_54_2),p.mkBVZeroExtend(52,varMap.get(mul_1),53),53)
                )
        });

        varMap.put(idLhs.getVariable(),mulResult);
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
        } else if (expr instanceof IdentifierExpression) {
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

    public FloatingPointEncoder(Prover p, ProverADT floatingPointADT, Precision precision)
    {
        this.p = p;
        this.floatingPointADT = floatingPointADT;
        this.floatingPointPrecision = precision;
        e = (precision == Precision.Single ? 8 : 11);
        f = (precision == Precision.Single ? 23 : 53);
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
    public ProverExpr mkDoublePE( ProverExpr sign, ProverExpr exponent,ProverExpr mantissa) {
            return mkDoublePE(sign, exponent, mantissa, floatingPointADT);
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
        ProverExpr sign, exponent,mantissa;

        IeeeFloatt ieeeOne = new IeeeFloatt(new IeeeFloatSpect(f-1, e));
        ieeeOne.fromDouble(value);
        sign = BVLit( new BigInteger(ieeeOne.get_sign() ? "1" : "0"),1);
        exponent = BVLit(ieeeOne.get_exponent().add(ieeeOne.getSpec().maxExponent()),e);
       
       //ieeeOne.get_exponent().doubleValue()
       // byte [] ex = ieeeOne.get_exponent().toByteArray();
       // byte [] ma = ieeeOne.get_fraction().toByteArray();
        mantissa = BVLit(ieeeOne.get_fraction(),f);
       //ieeeOne.get_fraction().add(BigInteger.ONE).doubleValue()
        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa });

        return  res;
    }
    private ProverExpr mkDoublePE( ProverExpr sign, ProverExpr exponent,ProverExpr mantissa, ProverADT floatingPointADT)
    {


        ProverExpr res = floatingPointADT.mkCtorExpr(0,new ProverExpr[]{sign, exponent,mantissa });

        return  res;
    }
}
