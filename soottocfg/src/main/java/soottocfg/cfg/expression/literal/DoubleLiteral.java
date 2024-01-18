package soottocfg.cfg.expression.literal;

import soottocfg.cfg.SourceLocation;
import soottocfg.cfg.expression.Expression;
import soottocfg.cfg.expression.IdentifierExpression;
import soottocfg.cfg.type.DoubleType;
import soottocfg.cfg.type.IntType;
import soottocfg.cfg.type.Type;
import soottocfg.cfg.variable.Variable;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class DoubleLiteral extends Expression implements Literal{
    private static final long serialVersionUID = 7913206010686231183L;

    private final Double value;

    private static final DoubleLiteral one = new DoubleLiteral(null, 1.0);
    private static final DoubleLiteral zero = new DoubleLiteral(null, 0.0);
    private static final DoubleLiteral minusOne = new DoubleLiteral(null, -1.0);

    public static DoubleLiteral one() {
        return one;
    }

    public static DoubleLiteral zero() {
        return zero;
    }

    public static DoubleLiteral minusOne() {
        return minusOne;
    }

    public DoubleLiteral(SourceLocation loc,Double value) {
        super(loc);
        this.value = value; //Long.valueOf(value);
    }
    public DoubleLiteral(SourceLocation loc, Long value) {
        super(loc);
        this.value = Double.longBitsToDouble(value); //Long.valueOf(value);
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

    public Double getValue() {
        return value;
    }

    @Override
    public Type getType() {
        return DoubleType.instance();
    }

    @Override
    public boolean equals(Object other) {
        if (other instanceof Double) {
            return ((DoubleLiteral) other).getValue().equals(this.value);
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
