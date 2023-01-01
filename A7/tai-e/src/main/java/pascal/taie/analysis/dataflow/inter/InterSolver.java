/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.util.collection.SetQueue;

import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    public Set<Node> getAllStmts() {
        return icfg.getNodes();
    }

    public Fact getInFact(Node n) {
        return result.getInFact(n);
    }

    private void initialize() {
        // TODO - finish me
        List<Node> entries = getEntries();
        for (Node entry : entries) {
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        }

        for (Node n : icfg) {
            if (!entries.contains(n)) {
                result.setInFact(n, analysis.newInitialFact());
                result.setOutFact(n, analysis.newInitialFact());
            }
        }
    }

    private void doSolve() {
        // TODO - finish me
        boolean changed = true;
        List<Node> entries = getEntries();
        List<Node> exits = getExits();

        while (changed) {
            changed = false;
            for (Node node : icfg) {
                if (! (entries.contains(node) || exits.contains(node))) {
                    Fact inFact = result.getInFact(node);
                    Fact outFact = result.getOutFact(node);
                    for (ICFGEdge<Node> inEdge : icfg.getInEdgesOf(node)) {
                        Node pred = inEdge.getSource();
                        Fact predOutFact = result.getOutFact(pred);
                        Fact outFactAfterEdge = analysis.transferEdge(inEdge, predOutFact);
                        analysis.meetInto(outFactAfterEdge, inFact);
                    }

                    if (analysis.transferNode(node, inFact, outFact)) {
                        changed  = true;
                    }

                    result.setOutFact(node, outFact);
                }
            }
        }
    }

    private List<Node> getEntries() {
        List<Node> entries = new LinkedList<>();
        List<Method> entryMethods = icfg.entryMethods().toList();
        for (Method m : entryMethods) {
            Node entry = icfg.getEntryOf(m);
            entries.add(entry);
        }

        return entries;
    }

    private List<Node> getExits() {
        List<Node> exits = new LinkedList<>();
        List<Method> entryMethods = icfg.entryMethods().toList();
        for (Method m : entryMethods) {
            Node exit = icfg.getExitOf(m);
            exits.add(exit);
        }

        return exits;
    }
}
