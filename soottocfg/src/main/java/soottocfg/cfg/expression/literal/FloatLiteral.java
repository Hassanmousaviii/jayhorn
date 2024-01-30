package soottocfg.cfg.expression.literal;

import soottocfg.cfg.SourceLocation;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.type.DoubleType;
import soottocfg.cfg.type.FloatType;
import soottocfg.cfg.type.Type;
import soottocfg.cfg.variable.Variable;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class FloatLiteral extends Expression implements Literal{
    private static final long serialVersionUID = 7913206010686231183L;

    private final Float value;

    private static final FloatLiteral one = new FloatLiteral(null, 1);
    private static final FloatLiteral zero = new FloatLiteral(null, 0);
    private static final FloatLiteral minusOne = new FloatLiteral(null, -1);

    public static FloatLiteral one() {
        return one;
    }

    public static FloatLiteral zero() {
        return zero;
    }

    public static FloatLiteral minusOne() {
        return minusOne;
    }

    public FloatLiteral(SourceLocation loc, Float value) {
        super(loc);
        this.value = value; //Long.valueOf(value);
    }
    public FloatLiteral(SourceLocation loc, int value) {
        super(loc);
        this.value = Float.intBitsToFloat(value); //Long.valueOf(value);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(value);
        return sb.toString();
    }

    @Override
    public Set<IdentifierExpression> getUseIdentifierExpressions() {
        return new HashSet<IdentifierExpression>();
    }

    @Override
    public Set<Variable> getDefVariables() {
        // because this can't happen on the left.
        Set<Variable> used = new HashSet<Variable>();
        return used;
    }

    public Float getValue() {
        return value;
    }

    @Override
    public Type getType() {
        return FloatType.instance();
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Double) {
            return ((FloatLiteral) other).getValue().equals(this.value);
        }
        return false;
    }

    @Override
    public int hashCode() {
        return value.hashCode();
    }

    @Override
    public Expression substitute(Map<Variable, Variable> subs) {
        return this;
    }

    @Override
    public Expression substituteVarWithExpression(Map<Variable, Expression> subs) {
        return this;
    }
}