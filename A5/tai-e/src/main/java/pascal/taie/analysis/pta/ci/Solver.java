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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.hasNode(method)) {
            callGraph.addReachableMethod(method);
            List<Stmt> stmts = method.getIR().getStmts();

            for (Stmt stmt : stmts) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Var v = stmt.getLValue();
            Obj obj = heapModel.getObj(stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(v), new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Var lv = stmt.getLValue();
            Var rv = stmt.getRValue();
            addPFGEdge(pointerFlowGraph.getVarPtr(rv), pointerFlowGraph.getVarPtr(lv));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var lv = stmt.getLValue();
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(lv));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                JField field = stmt.getFieldRef().resolve();
                Var rv = stmt.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(rv), pointerFlowGraph.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod targetMethod = resolveCallee(null, stmt);
                Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(stmt), stmt, targetMethod);
                if (callGraph.addEdge(edge)) {
                    addReachable(targetMethod);
                    passArgsToParamsAndRetVar(stmt, targetMethod);
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target) && (!source.getPointsToSet().isEmpty())) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();

            PointsToSet deltaPTS = propagate(pointer, pointsToSet);
            if (pointer instanceof VarPtr) {
                Var v = ((VarPtr) pointer).getVar();
                for (Obj obj : deltaPTS.getObjects()) {
                    // handle load
                    List<LoadField> loadFields = v.getLoadFields();
                    for (LoadField loadField : loadFields) {
                        Var lValue = loadField.getLValue();
                        JField field = loadField.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(instanceField, pointerFlowGraph.getVarPtr(lValue));
                    }

                    // handle store
                    List<StoreField> storeFields = v.getStoreFields();
                    for (StoreField storeField : storeFields) {
                        Var rValue = storeField.getRValue();
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(pointerFlowGraph.getVarPtr(rValue), instanceField);
                    }

                    // handle load array
                    List<LoadArray> loadArrays = v.getLoadArrays();
                    for (LoadArray loadArray : loadArrays) {
                        Var lValue = loadArray.getLValue();
                        ArrayIndex array = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(array, pointerFlowGraph.getVarPtr(lValue));
                    }

                    // handle store array
                    List<StoreArray> storeArrays = v.getStoreArrays();
                    for (StoreArray storeArray : storeArrays) {
                        Var rValue = storeArray.getRValue();
                        ArrayIndex array = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(pointerFlowGraph.getVarPtr(rValue), array);
                    }

                    // handle method call
                    processCall(v, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        Set<Obj> deltaObjs = new HashSet<>(pointsToSet.getObjects());
        Set<Obj> originObjs = pointer.getPointsToSet().getObjects();
        deltaObjs.removeAll(originObjs);
        PointsToSet deltaPTS = new PointsToSet();
        if (!deltaObjs.isEmpty()) {
            for (Obj obj : deltaObjs) {
                deltaPTS.addObject(obj);
            }
            for (Obj obj : deltaObjs) {
                pointer.getPointsToSet().addObject(obj);
            }
            Set<Pointer> succsOf = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer succ : succsOf) {
                workList.addEntry(succ, deltaPTS);
            }
        }
        return deltaPTS;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            JMethod targetMethod = resolveCallee(recv, invoke);
            // pass receive obj to this var
            Var MThis = targetMethod.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(MThis), new PointsToSet(recv));

            Edge<Invoke, JMethod> edge = new Edge<>(getCallKind(invoke), invoke, targetMethod);
            if (callGraph.addEdge(edge)) {
                addReachable(targetMethod);
                passArgsToParamsAndRetVar(invoke, targetMethod);
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }

    private void passArgsToParamsAndRetVar(Invoke invoke, JMethod targetMethod) {
        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
            Var arg = invoke.getInvokeExp().getArg(i);
            Var param = targetMethod.getIR().getParam(i);
            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
        }
        // pass return value
        Var lValue = invoke.getLValue();
        if (lValue != null) {
            for (Var retVar : targetMethod.getIR().getReturnVars()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(retVar), pointerFlowGraph.getVarPtr(lValue));
            }
        }
    }

    private CallKind getCallKind(Invoke invoke) {
        if (invoke.isInterface()) return CallKind.INTERFACE;
        if (invoke.isVirtual()) return CallKind.VIRTUAL;
        if (invoke.isSpecial()) return CallKind.SPECIAL;
        if (invoke.isStatic()) return CallKind.STATIC;
        if (invoke.isDynamic()) return CallKind.DYNAMIC;
        return CallKind.OTHER;
    }
}
