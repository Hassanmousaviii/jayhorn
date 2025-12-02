package jayhorn.solver.spacer;

import jayhorn.solver.*;


import com.microsoft.z3.*;

//import static jayhorn.solver.princess.PrincessProver.type2Sort; //????

/**
 * Class representing algebraic data-types
 */
public class SpacerADT implements ProverADT {

    private final DatatypeSort[] sorts;
    private final Context ctx;

    private final SpacerFun[] constructors;
    private final SpacerFun[][] selectors;
    private final SpacerFun[] sizeOps;

    private final String[] typeNames;


    public SpacerADT(Context ctx, DatatypeSort[] sorts, String[] typeNames) {
        this.ctx = ctx;
        this.sorts = sorts;
        this.typeNames = typeNames;

        // Initialize constructors and selectors arrays
        int maxCtors = 0;
        for (DatatypeSort sort : sorts) {
            maxCtors = Math.max(maxCtors, sort.getNumConstructors());
        }

        this.constructors = new FuncDecl[sorts.length][];
        this.selectors = new FuncDecl[sorts.length][][];

        // Extract constructors and selectors from Z3 datatypes
        for (int i = 0; i < sorts.length; i++) {
            int numCtors = sorts[i].getNumConstructors();
            constructors[i] = new FuncDecl[numCtors];
            selectors[i] = new FuncDecl[numCtors][];

            for (int j = 0; j < numCtors; j++) {
                constructors[i][j] = sorts[i].getConstructors()[j];

                int numSels = sorts[i].getAccessors()[j].length;
                selectors[i][j] = new FuncDecl[numSels];
                for (int k = 0; k < numSels; k++) {
                    selectors[i][j][k] = sorts[i].getAccessors()[j][k];
                }
            }
        }
    }

    public ProverType getType(int typeIndex) {
        return new PrincessADTType (adt.sorts().apply(typeIndex));
    }
//
//    @Override
//    public ProverExpr mkHavocExpr(int typeIndex) {
//        throw new RuntimeException("not implemented");
//    }
//
//    public ProverExpr mkCtorExpr(int ctorIndex, ProverExpr[] args) {
//        return constructors[ctorIndex].mkExpr(args);
//    }
//
//    public ProverExpr mkSelExpr(int ctorIndex, int selIndex, ProverExpr term) {
//        return selectors[ctorIndex][selIndex].mkExpr(new ProverExpr[] { term });
//    }
//
//    public ProverExpr mkTestExpr(int ctorIndex, ProverExpr term) {
//        return new FormulaExpr (adt.hasCtor(((PrincessProverExpr)term).toTerm(),
//                ctorIndex));
//    }
//
//    public ProverExpr mkSizeExpr(ProverExpr term) {
//        final ProverType type = term.getType();
//
//        if (type instanceof PrincessADTType) {
//            final int index = ((PrincessADTType)type).getTypeIndex();
//            return sizeOps[index].mkExpr(new ProverExpr[] { term });
//        }
//
//        throw new IllegalArgumentException();
//    }
//
    /**
     * Define an algebraic data-type with the given sort, constructor,
     * and selector names and types
     * @param typeNames namings of this ADT
     * @param ctorNames ADT constructors names
     * @param ctorTypes ADT constructors types
     * @param ctorArgTypes argument types of ADT constructors
     * @param selectorNames ADT selectors names
     * @return generated ProverADT
     */
    public static ProverADT mkADT(String[]       typeNames,
                                  String[]       ctorNames,
                                  int[]          ctorTypes,
                                  ProverType[][] ctorArgTypes,
                                  String[][]     selectorNames) {
        assert (ctorNames.length == ctorTypes.length &&
                ctorNames.length == ctorArgTypes.length &&
                ctorNames.length == selectorNames.length);

        final ArrayBuffer<String> sortNames = new ArrayBuffer<>();
        for (int i = 0; i < typeNames.length; ++i)
            sortNames.$plus$eq(typeNames[i]);

        final ArrayBuffer<Tuple2<String, ADT.CtorSignature>> ctors =
                new ArrayBuffer<>();
        for (int i = 0; i < ctorNames.length; ++i) {
            assert (ctorArgTypes[i].length == selectorNames[i].length);

            final ADT.ADTSort resSort = new ADT.ADTSort(ctorTypes[i]);

            final ArrayBuffer<Tuple2<String, ADT.CtorArgSort>> args =
                    new ArrayBuffer<>();
            for (int j = 0; j < ctorArgTypes[i].length; ++j) {
                final ProverType type = ctorArgTypes[i][j];
                final ADT.CtorArgSort argSort;
                if (type instanceof ADTTempType)
                    argSort = new ADT.ADTSort(((ADTTempType) type).typeIndex);
                else
                    argSort = new ADT.OtherSort(type2Sort(type));
                args.$plus$eq(new Tuple2(selectorNames[i][j], argSort));
            }

            ctors.$plus$eq(new Tuple2(ctorNames[i],
                    new ADT.CtorSignature(args, resSort)));
        }

        final ADT adt =
                new ADT(sortNames, ctors, ADT.TermMeasure$.MODULE$.Size(),
                        scala.Option$.MODULE$.empty());
        return new PrincessADT(adt);
    }

}
