package jayhorn.solver;

public class BitVectorType implements ProverType{
    public final int arity;


    public BitVectorType(int arity) {
        this.arity = arity;
    }

    @Override
    public String toString() {
        return "(_ BitVec " + arity + ")";
    }
}
