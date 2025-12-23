package jayhorn.solver.spacer;

import jayhorn.solver.*;
import com.microsoft.z3.*;

/**
 * Represents an ADT type in the Spacer prover
 */
public class SpacerADTType implements ProverADTType {

    private final DatatypeSort sort;
    private final int typeIndex;

    public SpacerADTType(DatatypeSort sort, int typeIndex) {
        this.sort = sort;
        this.typeIndex = typeIndex;
    }

    public DatatypeSort getSort() {
        return sort;
    }

    public int getTypeIndex() {
        return typeIndex;
    }
    @Override
    public String toString() {
        return sort.getName().toString();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof SpacerADTType)) return false;
        SpacerADTType other = (SpacerADTType) obj;
        return typeIndex == other.typeIndex && sort.equals(other.sort);
    }

    @Override
    public int hashCode() {
        return 31 * sort.hashCode() + typeIndex;
    }

    @Override
    public String getName() {
        return this.sort.getName().toString();
    }
}