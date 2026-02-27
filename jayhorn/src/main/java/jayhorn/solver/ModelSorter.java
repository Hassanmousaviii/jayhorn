package jayhorn.solver;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.regex.*;

/**
 * Sorts a Horn model (invarient.txt) according to the
 * clause dependency graph (DependencyGraph.txt).
 *
 * Usage:
 *   java ModelSorter invarient.txt DependencyGraph.txt [filterToken]
 *
 * Example:
 *   java ModelSorter invarient.txt DependencyGraph.txt d0_
 */
public class ModelSorter {

    /** One block from the model: predicate + formula text. */
    static class ModelEntry {
        final String pred;     // e.g. "<Main: void main(...>_Block7_14"
        final String header;   // full header line, including "/N:"
        final String body;     // the formula lines

        ModelEntry(String pred, String header, String body) {
            this.pred = pred;
            this.header = header;
            this.body = body;
        }

        @Override
        public String toString() {
            return header + System.lineSeparator() + body;
        }
    }

    public static void main(String[] args) throws IOException {
        if (args.length < 2) {
            System.err.println("Usage: java ModelSorter <modelFile> <depGraphFile> [filterToken]");
            System.exit(1);
        }
        String modelPath = args[0];
        String depPath   = args[1];
        String filterToken = (args.length >= 3) ? args[2] : null;

        Map<String, ModelEntry> model = parseModel(modelPath);
        Map<String, Set<String>> graph = parseDependencyGraph(depPath);

        // Ensure that all predicates that appear in model are nodes in the graph
        for (String p : model.keySet()) {
            graph.putIfAbsent(p, new HashSet<>());
        }

        List<String> topoOrder = topoSort(graph);

        // Print invariants in topo order, with optional filtering
        for (String pred : topoOrder) {
            ModelEntry e = model.get(pred);
            if (e == null) continue; // no invariant for this predicate

            if (filterToken != null && !e.body.contains(filterToken)) {
                // Skip blocks that are not related to the requested token (e.g. d0_)
                continue;
            }

            System.out.println("----------------------------------");
            System.out.println(e.header);
            System.out.println(e.body.trim());
            System.out.println();
        }
    }

    // ============== 1.1 Parse model file (invarient.txt) =================

    private static Map<String, ModelEntry> parseModel(String path) throws IOException {
        List<String> lines = Files.readAllLines(Paths.get(path));
        Map<String, ModelEntry> result = new HashMap<>();

        String currentHeader = null;
        StringBuilder body = new StringBuilder();
        String currentPred = null;

        for (String line : lines) {
            String trimmed = line.trim();

            // Block separator line: "----------------------------------"
            if (trimmed.startsWith("----------------------------------")) {
                // flush previous block, if any
                if (currentHeader != null && currentPred != null) {
                    result.put(currentPred,
                            new ModelEntry(currentPred, currentHeader, body.toString().trim()));
                }
                currentHeader = null;
                currentPred = null;
                body.setLength(0);
                continue;
            }

            // Header line: "<Main: void main(...)>_Block7_14/17:" or "Assert #0: Main.java, line 6/0:"
            if (trimmed.startsWith("<") || trimmed.startsWith("Assert")) {
                currentHeader = trimmed;
                currentPred = extractPredFromModelHeader(trimmed);
                body.setLength(0);
            } else {
                // part of body
                if (currentHeader != null) {
                    body.append(line).append(System.lineSeparator());
                }
            }
        }

        // last block (if file does not end with separator)
        if (currentHeader != null && currentPred != null) {
            result.put(currentPred,
                    new ModelEntry(currentPred, currentHeader, body.toString().trim()));
        }

        return result;
    }

    /**
     * Extract predicate key from a model header.
     * Examples:
     *  "<Main: void main(...>_Block7_14/17:" -> "<Main: void main(...>_Block7_14"
     *  "Assert #0: Main.java, line 6/0:"     -> "Assert #0: Main.java, line 6"
     */
    private static String extractPredFromModelHeader(String header) {
        int slash = header.indexOf('/');
        if (slash < 0) {
            // fallback: strip trailing colon
            int colon = header.indexOf(':');
            return (colon >= 0) ? header.substring(0, colon).trim() : header.trim();
        }
        return header.substring(0, slash).trim();
    }

    // ============== 1.2 Parse dependency graph ======================

    private static Map<String, Set<String>> parseDependencyGraph(String path) throws IOException {
        List<String> lines = Files.readAllLines(Paths.get(path));
        Map<String, Set<String>> graph = new HashMap<>();

        String currentHead = null;

        for (String line : lines) {
            String trimmed = line.trim();

            if (trimmed.startsWith("Clause:")) {
                currentHead = null; // will be set by the next head line
                continue;
            }

            // Head line of a clause
            if (trimmed.startsWith("<") || trimmed.startsWith("false :-") || trimmed.startsWith("Assert")) {
                // Only treat as head if we're inside a "Clause:" block AND line is not a "->" continuation
                if (!line.startsWith("    ->")) {
                    currentHead = extractPredFromClauseHead(trimmed);
                    graph.putIfAbsent(currentHead, new HashSet<>());
                }
                continue;
            }

            // Arrow line: "-> <Main: ...>_BlockX(..."
            if (trimmed.startsWith("->")) {
                if (currentHead == null) continue;
                String childHead = trimmed.substring(2).trim(); // remove "->"
                String childPred = extractPredFromClauseHead(childHead);
                if (childPred == null) continue;

                // Edge orientation: child -> currentHead
                graph.putIfAbsent(childPred, new HashSet<>());
                graph.get(childPred).add(currentHead);
            }
        }

        return graph;
    }

    /**
     * Extract predicate key from a clause head line in DependencyGraph.txt.
     *
     * Examples:
     *   "<Main: void main(...)>_Block7_14(... ) :- ..." ->
     *      "<Main: void main(...)>_Block7_14"
     *   "false :- Assert #0: Main.java, line 6." ->
     *      "Assert #0: Main.java, line 6"
     */
    private static String extractPredFromClauseHead(String headLine) {
        String s = headLine;

        // case 1: normal predicate "<Main: ...>_BlockX(..."
        int lt = s.indexOf('<');
        int paren = s.indexOf('(');
        int colonMinus = s.indexOf(":-");

        if (lt >= 0 && paren > lt) {
            // "<..>_BlockX(" -> take substring [lt, paren)
            String pred = s.substring(lt, paren).trim();
            return pred;
        }

        // case 2: "false :- Assert #0: Main.java, line 6."
        if (s.startsWith("false :-")) {
            int idx = s.indexOf("Assert");
            if (idx >= 0) {
                String rest = s.substring(idx).trim();
                // drop trailing dot, if any
                if (rest.endsWith(".")) rest = rest.substring(0, rest.length() - 1);
                return rest;
            }
        }

        // case 3: "Assert #0: Main.java, line 6 :- ..."
        if (s.startsWith("Assert")) {
            int idx = s.indexOf(":-");
            String rest = (idx >= 0) ? s.substring(0, idx) : s;
            return rest.trim();
        }

        // Fallback: nothing recognized
        return null;
    }

    // ============== 1.2 Topological sort ======================

    private static List<String> topoSort(Map<String, Set<String>> graph) {
        // Compute in-degree
        Map<String, Integer> indeg = new HashMap<>();
        for (String u : graph.keySet()) {
            indeg.putIfAbsent(u, 0);
        }
        for (Map.Entry<String, Set<String>> e : graph.entrySet()) {
            for (String v : e.getValue()) {
                indeg.put(v, indeg.getOrDefault(v, 0) + 1);
            }
        }

        // Kahn's algorithm
        Queue<String> q = new ArrayDeque<>();
        for (Map.Entry<String, Integer> e : indeg.entrySet()) {
            if (e.getValue() == 0) {
                q.add(e.getKey());
            }
        }

        List<String> order = new ArrayList<>();
        while (!q.isEmpty()) {
            String u = q.remove();
            order.add(u);
            for (String v : graph.getOrDefault(u, Collections.emptySet())) {
                int d = indeg.get(v) - 1;
                indeg.put(v, d);
                if (d == 0) q.add(v);
            }
        }

        // If there is a cycle, some nodes will still have indegree > 0.
        // Append remaining nodes in arbitrary order to keep algorithm total.
        if (order.size() < graph.size()) {
            for (String node : graph.keySet()) {
                if (!order.contains(node)) {
                    order.add(node);
                }
            }
        }

        return order;
    }
}
