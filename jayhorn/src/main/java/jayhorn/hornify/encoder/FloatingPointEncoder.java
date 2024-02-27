package jayhorn.hornify.encoder;

import com.google.common.base.Verify;
import com.sun.org.apache.xpath.internal.operations.Bool;
import jayhorn.hornify.HornHelper;
import jayhorn.solver.*;
import scala.Int;
import soottocfg.cfg.expression.BinaryExpression;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.expression.literal.DoubleLiteral;
import soottocfg.cfg.expression.literal.StringLiteral;
import soottocfg.cfg.type.ReferenceType;
import soottocfg.cfg.variable.Variable;

import javax.annotation.Nullable;
import java.math.BigInteger;
import java.util.Map;

public class FloatingPointEncoder {

    public enum Precision{
        Single,
        Double
    }
    private Prover p;
    private ProverADT floatingPointADT;

    private Precision floatingPointPrecision;

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
    public FloatingPointEncoder.EncodingFacts handleFloatingPointExpr(Expression e, Map<Variable, ProverExpr> varMap) {

        if (e instanceof BinaryExpression) {
            final BinaryExpression be = (BinaryExpression) e;
            Expression leftExpr = be.getLeft();
            Expression rightExpr = be.getRight();
            switch (be.getOp()) {
                case ToDouble:
                case ToFloat:
                    return mkToDoubleFromExpression(leftExpr, rightExpr,varMap);
                default: return null;

            }
        }
        return null;
    }
    public FloatingPointEncoder.EncodingFacts mkToDoubleFromExpression(Expression DoubleExpr, Expression lhsRefExpr,
                                                                Map<Variable, ProverExpr> varMap) {
        ReferenceType lhsRefExprType = (ReferenceType) lhsRefExpr.getType();

        final ProverExpr internalDouble = selectFloatingPoint(DoubleExpr, varMap);
        if (internalDouble == null)
            return null;
        ProverExpr result = mkRefHornVariable(internalDouble.toString(), lhsRefExprType);
        ProverExpr resultString = selectFloatingPoint(result);
        return new FloatingPointEncoder.EncodingFacts(null, null, result,
                p.mkAnd(mkNotNullConstraint(result), p.mkEq(resultString, internalDouble))
        );
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
