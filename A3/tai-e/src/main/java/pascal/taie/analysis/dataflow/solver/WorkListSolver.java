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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>();
        for (Node node : cfg) {
            if (!(cfg.isExit(node) || cfg.isEntry(node))) {
                workList.add(node);
            }
        }

        while(!workList.isEmpty()) {
            Node node = workList.peek();
            workList.remove();

            Fact inFact = result.getInFact(node);
            Fact outFact = result.getOutFact(node);
            Set<Node> predsOf = cfg.getPredsOf(node);
            for (Node pred : predsOf) {
                Fact outPred = result.getOutFact(pred);
                analysis.meetInto(outPred, inFact);
            }

            if (analysis.transferNode(node, inFact, outFact)) {
                Set<Node> succsOf = cfg.getSuccsOf(node);
                for (Node succ : succsOf) {
                    if (!cfg.isExit(succ)) {
                        workList.add(succ);
                    }
                }
            }
            result.setOutFact(node, outFact);
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        // TODO - finish me
        Queue<Node> workList = new LinkedList<>();
        for (Node node : cfg) {
            if (!(cfg.isExit(node) || cfg.isEntry(node))) {
                workList.add(node);
            }
        }

        while (!workList.isEmpty()) {
            Node node = workList.peek();
            workList.remove();

            Fact inFact = result.getInFact(node);
            Fact outFact = result.getOutFact(node);
            Set<Node> succsOf = cfg.getSuccsOf(node);
            for (Node succ : succsOf) {
                Fact inSucc = result.getInFact(succ);
                analysis.meetInto(inSucc, outFact);
            }

            if (analysis.transferNode(node, inFact, outFact)) {
                Set<Node> predsOf = cfg.getPredsOf(node);
                for (Node pred : predsOf) {
                    if (!cfg.isEntry(pred)) {
                        workList.add(pred);
                    }
                }
            }
            result.setInFact(node, inFact);
        }
    }
}
