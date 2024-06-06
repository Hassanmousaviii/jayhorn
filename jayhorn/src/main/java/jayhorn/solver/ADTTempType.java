package jayhorn.solver;


import java.util.HashMap;

public class ADTTempType implements ProverType {

	private static final HashMap<Integer, ADTTempType> idx2type = new HashMap<Integer, ADTTempType>(1);
	public static final int ListADTTypeIndex = 0;

	public static final int FloatingPointADTTypeIndex = 1;
	public static final int DoubleFloatingPointADTTypeIndex = 2;

	public static final int TempFloatingPointADTTypeIndex = 3;
	public static final int TempDoubleFloatingPointADTTypeIndex = 4;

	public static final int TempFloatingPointOperandsADTTypeIndex = 5;
	public static final int TempDoubleFloatingPointOperandsADTTypeIndex = 6;

	public final int typeIndex;

	/**
	 * Temporary type representing the n'th ADT type; this is only used
	 * for defining ADTs
	 */
	public static ADTTempType getADTTempType(int ti) {
		if (!idx2type.containsKey(ti)) {
			idx2type.put(ti, new ADTTempType(ti));
		}
		return idx2type.get(ti);
	}

	public ADTTempType(int typeIndex) {
		this.typeIndex = typeIndex;
	}

	@Override
	public String toString() {
		return "ADT[" + typeIndex + "]";
	}

	@Override
	public int hashCode() {
		// resolve FindBugs Report:
		//		HE_EQUALS_USE_HASHCODE: Class defines equals() and uses Object.hashCode()
		return this.typeIndex;
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof  ADTTempType) {
			return this.typeIndex == ((ADTTempType)o).typeIndex;
		}
		return false;
	}

}
