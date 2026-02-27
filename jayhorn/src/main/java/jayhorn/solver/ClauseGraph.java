
package jayhorn.solver;

import java.util.*;
import lazabs.horn.global.HornClause;
import java.util.function.Predicate;

import java.util.*;



import java.util.*;

public class ClauseGraph {

    private final Map<ProverHornClause, Set<ProverHornClause>> edges = new HashMap<>();

    public void addNode(ProverHornClause c) {
        edges.computeIfAbsent(c, k -> new HashSet<>());
    }

    public void addEdge(ProverHornClause from, ProverHornClause to) {
        addNode(from);
        addNode(to);
        edges.get(from).add(to);
    }

    public Set<ProverHornClause> successors(ProverHornClause c) {
        return edges.getOrDefault(c, Collections.emptySet());
    }

    public Map<ProverHornClause, Set<ProverHornClause>> getEdges() {
        return edges;
    }

    public boolean hasSelfLoop(ProverHornClause c) {
        return successors(c).contains(c);
    }
    public void prettyPrint() {
        System.out.println("=== Clause Dependency Graph ===");

        edges.forEach((from, targets) -> {
            System.out.println("Clause:");
            System.out.println("  " + from);

            if (targets.isEmpty()) {
                System.out.println("    -> (no outgoing edges)");
            } else {
                for (ProverHornClause to : targets) {
                    System.out.println("    -> " + to);
                }
            }
            System.out.println();
        });
    }
    public List<ProverHornClause> topologicalOrder() {
        // Compute indegree for each node
        Map<ProverHornClause, Integer> indegree = new HashMap<>();

        // Ensure all nodes appear with at least 0
        for (ProverHornClause c : edges.keySet()) {
            indegree.putIfAbsent(c, 0);
            for (ProverHornClause succ : edges.get(c)) {
                indegree.put(succ, indegree.getOrDefault(succ, 0) + 1);
            }
        }

        // Queue of nodes with no incoming edges
        Deque<ProverHornClause> queue = new ArrayDeque<>();
        for (Map.Entry<ProverHornClause, Integer> e : indegree.entrySet()) {
            if (e.getValue() == 0) {
                queue.add(e.getKey());
            }
        }

        List<ProverHornClause> order = new ArrayList<>();

        while (!queue.isEmpty()) {
            ProverHornClause c = queue.removeFirst();
            order.add(c);

            for (ProverHornClause succ : edges.getOrDefault(c, Collections.emptySet())) {
                int deg = indegree.get(succ) - 1;
                indegree.put(succ, deg);
                if (deg == 0) {
                    queue.addLast(succ);
                }
            }
        }

        // If there is a cycle, some nodes still have indegree > 0
        int totalNodes = indegree.size();
        if (order.size() < totalNodes) {
            // add remaining nodes at the end (they are in cycles)
            for (Map.Entry<ProverHornClause, Integer> e : indegree.entrySet()) {
                if (e.getValue() > 0 && !order.contains(e.getKey())) {
                    order.add(e.getKey());
                }
            }
        }

        return order;
    }
    public void prettyPrintTopological() {
        List<ProverHornClause> order = topologicalOrder();

        System.out.println("=== Clause order (DAG-style) ===");

        int line = 1;
        for (ProverHornClause c : order) {
            System.out.println(line + ": " + c.toString());
            line++;
        }

        System.out.println();
    }

}


