package jayhorn.solver;

import java.util.*;

public final class ClauseGraphBuilder {

    private ClauseGraphBuilder() {
        // utility class
    }

    public static ClauseGraph buildClauseGraph(List<ProverHornClause> clauses) {
        ClauseGraph graph = new ClauseGraph();

        // 1) Index clauses by head predicate symbol (ProverFun)
        Map<ProverFun, List<ProverHornClause>> headIndex = new HashMap<>();

        for (ProverHornClause clause : clauses) {
            graph.addNode(clause);

            ProverFun headFun = clause.getHeadFun();
            if (headFun != null) {           // head = false ⇒ null, skip as target
                headIndex
                        .computeIfAbsent(headFun, k -> new ArrayList<>())
                        .add(clause);
            }
        }

        // 2) For each clause, connect body predicate symbols to matching heads
        for (ProverHornClause from : clauses) {

            int arity = from.getArity();      // number of body literals

            for (int i = 0; i < arity; i++) {
                ProverFun bodyFun = from.getBodyFun(i);
                if (bodyFun == null) {
                    continue; // just in case; normally bodyFun should be non-null
                }

                List<ProverHornClause> targets =
                        headIndex.getOrDefault(bodyFun, Collections.emptyList());

                for (ProverHornClause to : targets) {
                    graph.addEdge(from, to);
                }
            }
        }

        return graph;
    }
}
