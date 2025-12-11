package jayhorn.solver.spacer;

import jayhorn.solver.*;
import com.microsoft.z3.*;

/**
 * Class representing algebraic data-types
 */
public class SpacerADT implements ProverADT {

    private final DatatypeSort[] sorts;
    private final Context ctx;

    private final SpacerFun[][] constructors;
    private final SpacerFun[][][] selectors;
    private final SpacerFun[][] recognizers;
    private final String[] typeNames;

    public SpacerADT(Context ctx, DatatypeSort[] sorts, String[] typeNames) {
        this.ctx = ctx;
        this.sorts = sorts;
        this.typeNames = typeNames;

        // Initialize constructors, selectors, and recognizers arrays
        this.constructors = new SpacerFun[sorts.length][];
        this.selectors = new SpacerFun[sorts.length][][];
        this.recognizers = new SpacerFun[sorts.length][];

        for (int i = 0; i < sorts.length; i++) {
            int numCtors = sorts[i].getNumConstructors();
            constructors[i] = new SpacerFun[numCtors];
            selectors[i] = new SpacerFun[numCtors][];
            recognizers[i] = new SpacerFun[numCtors];

            for (int j = 0; j < numCtors; j++) {
                FuncDecl ctorDecl = sorts[i].getConstructors()[j];
                constructors[i][j] = new SpacerFun(
                        ctorDecl,
                        ctx,
                        new SpacerADTType(sorts[i], i)
                );

                // Wrap recognizer (tester)
                FuncDecl recogDecl = sorts[i].getRecognizers()[j];
                recognizers[i][j] = new SpacerFun(recogDecl, ctx, BoolType.INSTANCE);

                // Wrap selectors
                FuncDecl[] accessorDecls = sorts[i].getAccessors()[j];
                int numSels = accessorDecls.length;
                selectors[i][j] = new SpacerFun[numSels];
                for (int k = 0; k < numSels; k++) {
                    FuncDecl selDecl = accessorDecls[k];
                    // Note: We need access to SpacerProver instance to call pack()
                    // For now, we'll handle the type conversion inline
                    Sort selSort = selDecl.getRange();
                    ProverType selType;
                    try {
                        if (selSort.equals(ctx.getIntSort())) {
                            selType = IntType.INSTANCE;
                        } else if (selSort.equals(ctx.getBoolSort())) {
                            selType = BoolType.INSTANCE;
                        } else if (selSort instanceof DatatypeSort) {
                            // Find which ADT type this is
                            int typeIdx = findSortIndex(selSort);
                            selType = new SpacerADTType((DatatypeSort)selSort, typeIdx);
                        } else if (selSort instanceof ArraySort) {
                            ArraySort as = (ArraySort) selSort;
                            // Recursive conversion needed - simplified for now
                            throw new RuntimeException("Array selectors not yet implemented");
                        } else {
                            throw new RuntimeException("Unknown selector type: " + selSort);
                        }
                    } catch (Exception e) {
                        throw new RuntimeException("Error determining selector type: " + e.getMessage());
                    }
                    selectors[i][j][k] = new SpacerFun(selDecl, ctx, selType);
                }
            }
        }
    }

    @Override
    public ProverType getType(int typeIndex) {
        return new SpacerADTType(sorts[typeIndex], typeIndex);
    }

    @Override
    public ProverExpr mkHavocExpr(int typeIndex) {
        throw new RuntimeException("not implemented");
    }

    @Override
    public ProverExpr mkCtorExpr(int ctorIndex, ProverExpr[] args) {
        // Find which type this constructor belongs to
        int typeIndex = findTypeForConstructor(ctorIndex);
        int localCtorIndex = getLocalConstructorIndex(ctorIndex);

        return constructors[typeIndex][localCtorIndex].mkExpr(args);
    }

    @Override
    public ProverExpr mkSelExpr(int ctorIndex, int selIndex, ProverExpr term) {
        int typeIndex = findTypeForConstructor(ctorIndex);
        int localCtorIndex = getLocalConstructorIndex(ctorIndex);

        return selectors[typeIndex][localCtorIndex][selIndex].mkExpr(new ProverExpr[] { term });
    }

    @Override
    public ProverExpr mkTestExpr(int ctorIndex, ProverExpr term) {
        int typeIndex = findTypeForConstructor(ctorIndex);
        int localCtorIndex = getLocalConstructorIndex(ctorIndex);

        return recognizers[typeIndex][localCtorIndex].mkExpr(new ProverExpr[] { term });
    }

    @Override
    public ProverExpr mkSizeExpr(ProverExpr term) {
        final ProverType type = term.getType();

        if (type instanceof SpacerADTType) {
            // Z3 doesn't have built-in size for ADTs like Princess does
            // You would need to define a custom size function
            throw new UnsupportedOperationException("ADT size not directly supported in Z3");
        }

        throw new IllegalArgumentException("Term is not of ADT type");
    }

    private int findTypeForConstructor(int ctorIndex) {
        // This assumes global constructor indexing across all types
        int count = 0;
        for (int i = 0; i < constructors.length; i++) {
            if (ctorIndex < count + constructors[i].length) {
                return i;
            }
            count += constructors[i].length;
        }
        throw new IllegalArgumentException("Constructor index out of bounds: " + ctorIndex);
    }

    private int findSortIndex(Sort sort) {
        for (int i = 0; i < sorts.length; i++) {
            if (sorts[i].equals(sort)) {
                return i;
            }
        }
        return -1; // Not found in our ADT sorts
    }

    private int getLocalConstructorIndex(int ctorIndex) {
        // Convert global constructor index to local index within its type
        int count = 0;
        for (int i = 0; i < constructors.length; i++) {
            if (ctorIndex < count + constructors[i].length) {
                return ctorIndex - count;
            }
            count += constructors[i].length;
        }
        throw new IllegalArgumentException("Constructor index out of bounds: " + ctorIndex);
    }

//    /**
//     * Define an algebraic data-type with the given sort, constructor,
//     * and selector names and types
//     * @param ctx Z3 context
//     * @param typeNames namings of this ADT
//     * @param ctorNames ADT constructors names
//     * @param ctorTypes ADT constructors types (which type each constructor belongs to)
//     * @param ctorArgTypes argument types of ADT constructors
//     * @param selectorNames ADT selectors names
//     * @return generated ProverADT
//     */
//    public static ProverADT mkADT(Context ctx,
//                                  String[] typeNames,
//                                  String[] ctorNames,
//                                  int[] ctorTypes,
//                                  ProverType[][] ctorArgTypes,
//                                  String[][] selectorNames) {
//        assert (ctorNames.length == ctorTypes.length &&
//                ctorNames.length == ctorArgTypes.length &&
//                ctorNames.length == selectorNames.length);
//
//        int numTypes = typeNames.length;
//
//        Constructor[][] ctorsByType = new Constructor[numTypes][];
//
//        for (int t = 0; t < numTypes; t++) {
//            int numCtors = 0;
//            for (int i = 0; i < ctorTypes.length; i++) {
//                if (ctorTypes[i] == t) numCtors++;
//            }
//
//            ctorsByType[t] = new Constructor[numCtors];
//            int ctorIdx = 0;
//
//            for (int i = 0; i < ctorNames.length; i++) {
//                if (ctorTypes[i] == t) {
//                    // Build constructor
//                    String[] selNames = selectorNames[i];
//                    Sort[] selSorts = new Sort[ctorArgTypes[i].length];
//                    int[] selRefs = new int[ctorArgTypes[i].length];
//
//                    for (int j = 0; j < ctorArgTypes[i].length; j++) {
//                        ProverType argType = ctorArgTypes[i][j];
//                        if (argType instanceof ADTTempType) {
//                            // Recursive reference to another ADT type
//                            selRefs[j] = ((ADTTempType) argType).typeIndex;
//                            selSorts[j] = null; // Will be resolved by Z3
//                        } else {
//                            selRefs[j] = 0; // TODO: should this be -1?
//                            // Convert ProverType to Z3 Sort
//                            if (argType instanceof IntType) {
//                                selSorts[j] = ctx.getIntSort();
//                            } else if (argType instanceof BoolType) {
//                                selSorts[j] = ctx.getBoolSort();
//                            } else if (argType instanceof ArrayType) {
//                                selSorts[j] = ((SpacerArrayType) argType).getSort();
//                            } else if (argType instanceof SpacerADTType) {
//                                selSorts[j] = ((SpacerADTType) argType).getSort();
//                            } else {
//                                throw new RuntimeException("Unknown ProverType: " + argType);
//                            }
//                        }
//                    }
//
//                    ctorsByType[t][ctorIdx] = ctx.mkConstructor(
//                            ctorNames[i],
//                            "is_" + ctorNames[i],
//                            selNames,
//                            selSorts,
//                            selRefs
//                    );
//                    ctorIdx++;
//                }
//            }
//        }
//
//        // Create the mutually recursive datatypes
//        DatatypeSort[] sorts = ctx.mkDatatypeSorts(typeNames, ctorsByType);
//
//        return new SpacerADT(ctx, sorts, typeNames);
//    }

    /**
     * Simplified method for creating a single-type ADT with a single constructor
     * @param ctx Z3 context
     * @param typeName name of the ADT type
     * @param ctorArgTypes argument types for the constructor
     * @param selectorNames selector names for the constructor arguments
     * @return generated ProverADT
     */
    public static ProverADT mkSimpleADT(Context ctx,
                                        String typeName,
                                        String ctorName,
                                        ProverType[] ctorArgTypes,
                                        String[] selectorNames) {
        // Convert ProverType[] to Z3 Sort[]
        Sort[] selectorSorts = new Sort[ctorArgTypes.length];
        int[] selectorRefs = new int[ctorArgTypes.length];


        for (int i = 0; i < ctorArgTypes.length; i++) {
            selectorRefs[i] = 0;
            ProverType argType = ctorArgTypes[i];
            if (argType instanceof IntType) {
                selectorSorts[i] = ctx.getIntSort();
            } else if (argType instanceof BoolType) {
                selectorSorts[i] = ctx.getBoolSort();
            } else if (argType instanceof SpacerArrayType) {
                selectorSorts[i] = ((SpacerArrayType) argType).getSort();
            } else if (argType instanceof SpacerADTType) {
                selectorSorts[i] = ((SpacerADTType) argType).getSort();
            } else if (argType instanceof BitVectorType) {
                selectorSorts[i] = ctx.mkBitVecSort(((BitVectorType) argType).arity());
            } else if (argType instanceof ADTTempType) {
                // Recursive reference
                selectorSorts[i] = null;
                selectorRefs[i] = ((ADTTempType) argType).typeIndex;
            } else {
                throw new RuntimeException("Unknown ProverType: " + argType);
            }
        }
        Constructor ctor = ctx.mkConstructor(
                typeName,              // Constructor name
                ctorName,             // Recognizer name
                selectorNames,         // Selector names
                selectorSorts,         // Selector sorts
                selectorRefs           // Selector sort refs
        );

        // Create the datatype
        DatatypeSort[] sorts = ctx.mkDatatypeSorts(
                new String[]{typeName},     // Type names
                new Constructor[][]{{ctor}} // Constructors for each type
        );

        // Return wrapped ADT
        return new SpacerADT(ctx, sorts, new String[]{typeName});
    }
}