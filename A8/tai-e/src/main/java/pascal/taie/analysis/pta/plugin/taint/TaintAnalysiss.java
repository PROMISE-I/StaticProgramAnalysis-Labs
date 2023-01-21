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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Pair;

import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private ArgsTaintPointerFlowGraph argsTaintPointerFlowGraph;

    private Set<Pair<Invoke, Pair<CSVar, Integer>>> sinkInfos;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        argsTaintPointerFlowGraph = new ArgsTaintPointerFlowGraph();
        sinkInfos = new HashSet<>();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    static class ArgsTaintPointerFlowGraph {

        /**
         * Map from a pointer (node) to its successors in PFG.
         */
        private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

        /**
         * Adds an edge (source -> target) to this PFG.
         *
         * @return true if this PFG changed as a result of the call,
         * otherwise false.
         */
        boolean addEdge(Pointer source, Pointer target) {
            return successors.put(source, target);
        }

        /**
         * @return successors of given pointer in the PFG.
         */
        Set<Pointer> getSuccsOf(Pointer pointer) {
            return successors.get(pointer);
        }
    }

    // TODO - finish me
    public void transferTaintOfArgs(Pointer pointer, PointsToSet diffPTS) {
        for (CSObj csObj : diffPTS.getObjects()) {
            if (manager.isTaint(csObj.getObject())) {
                for (Pointer success : argsTaintPointerFlowGraph.getSuccsOf(pointer)) {
                    changeTaintTypeAndPropagate(csObj, success);
                }
            }
        }
    }

    public void analyzeTaintOnCall(Invoke stmt, CSVar csBase, CSObj recvObj) {
        Context curCtx = csBase.getContext();
        // result var
        Var result = stmt.getLValue();
        if (result != null) {
            CSVar csResult = csManager.getCSVar(curCtx, result);
            /* analyze source */
            analyzeSource(stmt, recvObj, csResult);
            /* analyze taint transfer */
            analyzeBaseToResult(stmt, csBase, csResult);
            analyzeArgToBase(stmt, csBase);
            analyzeArgToResult(stmt, csResult);
            /* analyze sink */
            analyzeSink(stmt, recvObj, curCtx);
        } else {
            /* analyze taint transfer */
            analyzeArgToBase(stmt, csBase);
            /* analyze sink */
            analyzeSink(stmt, recvObj, curCtx);
        }
    }


    public void analyzeTaintOnStaticCall(Invoke stmt, Context curCtx) {
        // result var
        Var result = stmt.getLValue();
        if (result != null) {
            CSVar csResult = csManager.getCSVar(curCtx, result);
            /* analyze source */
            analyzeSource(stmt, null, csResult);
            /* analyze taint transfer */
            analyzeArgToResult(stmt, csResult);
            /* analyze sink */
            analyzeSink(stmt, null, curCtx);
        } else {
            /* analyze sink */
            analyzeSink(stmt, null, curCtx);
        }
    }

    private void analyzeSource(Invoke invokeStmt, CSObj recv, CSVar csResult) {
        JMethod method = solver.resolveCallee(recv, invokeStmt);
        Type returnType = method.getReturnType();

        Source source = new Source(method, returnType);
        if (config.getSources().contains(source)) { // TODO may fail due to different reference with the same value
            Obj taintObj = manager.makeTaint(invokeStmt, returnType);
            CSObj taintCSObj = csManager.getCSObj(emptyContext, taintObj);
            solver.addWork(csResult, PointsToSetFactory.make(taintCSObj));
        }
    }

    private void analyzeBaseToResult(Invoke stmt, CSVar csBase, CSVar csResult) {
        JMethod method = stmt.getMethodRef().resolve();
        Type returnType = method.getReturnType();

        TaintTransfer baseToResult = new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, returnType);
        if (config.getTransfers().contains(baseToResult)) {
            addArgsTaintPFGEdge(csBase, csResult);
        }
    }

    private void analyzeArgToBase(Invoke invokeStmt, CSVar csBase) {
        JMethod method = invokeStmt.getMethodRef().resolve();
        Type returnType = method.getReturnType();
        Context curCtx = csBase.getContext();

        for (int argIdx = 0; argIdx < invokeStmt.getInvokeExp().getArgCount(); argIdx++) {
            Var arg = invokeStmt.getInvokeExp().getArg(argIdx);
            CSVar csArg = csManager.getCSVar(curCtx, arg);

            TaintTransfer argToBase = new TaintTransfer(method, argIdx, TaintTransfer.BASE, returnType);
            if (config.getTransfers().contains(argToBase)) {
                addArgsTaintPFGEdge(csArg, csBase);
            }
        }
    }

    private void analyzeArgToResult(Invoke invokeStmt, CSVar csResult) {
        JMethod method = invokeStmt.getMethodRef().resolve();
        Type returnType = method.getReturnType();
        Context curCtx = csResult.getContext();

        for (int argIdx = 0; argIdx < invokeStmt.getInvokeExp().getArgCount(); argIdx++) {
            Var arg = invokeStmt.getInvokeExp().getArg(argIdx);
            CSVar csArg = csManager.getCSVar(curCtx, arg);

            TaintTransfer argToResult = new TaintTransfer(method, argIdx, TaintTransfer.RESULT, returnType);
            if (config.getTransfers().contains(argToResult)) {
                addArgsTaintPFGEdge(csArg, csResult);
            }
        }
    }

    private void analyzeSink(Invoke invokeStmt, CSObj recv, Context curCtx) {
        JMethod method = solver.resolveCallee(recv, invokeStmt);

        for (int argIdx = 0; argIdx < invokeStmt.getInvokeExp().getArgCount(); argIdx++) {
            Var arg = invokeStmt.getInvokeExp().getArg(argIdx);
            CSVar csArg = csManager.getCSVar(curCtx, arg);

            Sink sink = new Sink(method, argIdx);
            if (config.getSinks().contains(sink)) {
                sinkInfos.add(new Pair<>(invokeStmt, new Pair<>(csArg, argIdx)));
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        for (Pair<Invoke, Pair<CSVar, Integer>> sinkInfo : sinkInfos) {
            Invoke sink = sinkInfo.first();
            CSVar csArg = sinkInfo.second().first();
            int argIdx = sinkInfo.second().second();

            Set<CSObj> csArgPTS = result.getPointsToSet(csArg);
            for (CSObj csObj : csArgPTS) {
                if (manager.isTaint(csObj.getObject())) {
                    Invoke source = manager.getSourceCall(csObj.getObject());
                    TaintFlow taintFlow = new TaintFlow(source, sink, argIdx);
                    taintFlows.add(taintFlow);
                }
            }
        }
        return taintFlows;
    }

    /**
     * Adds an edge "source -> target" to the args taint PFG.
     */
    private void addArgsTaintPFGEdge(Pointer source, Pointer target) {
        PointsToSet sourcePTS = source.getPointsToSet();
        if (argsTaintPointerFlowGraph.addEdge(source, target) && (!sourcePTS.isEmpty())) {
            for (CSObj csObj : sourcePTS.getObjects()) {
                if (manager.isTaint(csObj.getObject())) {
                    changeTaintTypeAndPropagate(csObj, target);
                }
            }
        }
    }

    private void changeTaintTypeAndPropagate(CSObj sourceCSTaint, Pointer target) {
        Invoke source = manager.getSourceCall(sourceCSTaint.getObject());
        Type targetType = target.getType();
        Obj targetTaint = manager.makeTaint(source, targetType);

        CSObj targetCSTaint = csManager.getCSObj(emptyContext, targetTaint);
        solver.addWork(target, PointsToSetFactory.make(targetCSTaint));
    }
}
