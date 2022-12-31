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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(new StmtProcessor(csMethod));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            /* csVar = new T(); */
            // 通过堆模型获得对象，并通过 csManger 获得CSVar
            CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
            // 通过堆模型获得对象，并通过 csManger 获得原本上下文，再获得新的上下文，最后得到csObj
            CSMethod csMethod = csManager.getCSMethod(context, stmt.getContainer());
            Obj obj = heapModel.getObj(stmt);
            Context newContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(newContext, obj);
            // 加入 worklist
            workList.addEntry(csVar, PointsToSetFactory.make(csObj));

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) {
            /* lCsVar = rCsVar; */
            CSVar rCsVar = csManager.getCSVar(context, stmt.getRValue());
            CSVar lCsVar = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(rCsVar, lCsVar);

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) {
            /* x = T.f; */
            if (stmt.isStatic()) {
                StaticField staticField = csManager.getStaticField(stmt.getFieldRef().resolve());
                CSVar lCSVar = csManager.getCSVar(context, stmt.getLValue());

                addPFGEdge(staticField, lCSVar);
            }

            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) {
            /* T.f = x; */
            if (stmt.isStatic()) {
                CSVar csVar = csManager.getCSVar(context, stmt.getRValue());
                StaticField staticField = csManager.getStaticField(stmt.getFieldRef().resolve());

                addPFGEdge(csVar, staticField);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) {
            /* (x = ) T.m(); */
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt); // 解析方法签名
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt); // 获得上下文调用点

                Context newContext = contextSelector.selectContext(csCallSite, method); // 选择新的上下文
                CSMethod csMethod = csManager.getCSMethod(newContext, method);  // 组成上下文方法

                Edge<CSCallSite, CSMethod> callEdge = new Edge<>(CallKind.STATIC, csCallSite, csMethod);
                if (callGraph.addEdge(callEdge)) {
                    addReachable(csMethod);
                    passArgsAndRetVar(stmt, method, context, newContext);
                }
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        // TODO 源指针和目标指针的指向关系集应该不能直接赋值？
        PointsToSet sourcePTS = source.getPointsToSet();
        PointsToSet targetPTS = PointsToSetFactory.make();
        if (pointerFlowGraph.addEdge(source, target) && (!sourcePTS.isEmpty())) {
            targetPTS.addAll(sourcePTS);
            workList.addEntry(target, targetPTS);
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
            PointsToSet newPTS = entry.pointsToSet();
            PointsToSet diffPTS = propagate(pointer, newPTS);
            if (pointer instanceof CSVar) {
                CSVar csVar = (CSVar) pointer;
                for (CSObj csObj : diffPTS.getObjects()) {
                    Context context = csVar.getContext();
                    // handle field load
                    for (LoadField stmt : csVar.getVar().getLoadFields()) {
                        /* y = x.f */
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(csObj, field);
                        CSVar lCSVar = csManager.getCSVar(context, stmt.getLValue());

                        addPFGEdge(instanceField, lCSVar);
                    }

                    // handle array load
                    for (LoadArray stmt : csVar.getVar().getLoadArrays()) {
                        /* y = x[i] */
                        ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                        CSVar lCSVar = csManager.getCSVar(context, stmt.getLValue());

                        addPFGEdge(arrayIndex, lCSVar);
                    }

                    // handle field store
                    for (StoreField stmt : csVar.getVar().getStoreFields()) {
                        /* x.f = y */
                        CSVar rCSVar = csManager.getCSVar(context, stmt.getRValue());
                        JField field = stmt.getFieldRef().resolve();
                        InstanceField instanceField = csManager.getInstanceField(csObj, field);

                        addPFGEdge(rCSVar, instanceField);
                    }

                    // handle array store
                    for (StoreArray stmt : csVar.getVar().getStoreArrays()) {
                        /* x[i] = y */
                        CSVar rCSVar = csManager.getCSVar(context, stmt.getRValue());
                        ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);

                        addPFGEdge(rCSVar, arrayIndex);
                    }

                    // handle method invocation
                    processCall(csVar, csObj);
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
        PointsToSet diffPTS = PointsToSetFactory.make();

        Set<CSObj> objects = new HashSet<>(pointsToSet.getObjects());
        objects.removeAll(pointer.getPointsToSet().getObjects());
        if (!objects.isEmpty()) {
            for (CSObj csObj : objects) {
                diffPTS.addObject(csObj);   // 加入指向关系差集
                pointer.getPointsToSet().addObject(csObj);  // 加入指针自己的指向关系集合
            }
            for (Pointer success : pointerFlowGraph.getSuccsOf(pointer)) {
                // TODO 需要重新，以防 PointsToSet.getObjects()指向同一个对象
                workList.addEntry(success, diffPTS);
            }
        }
        return diffPTS;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Context context = recv.getContext();
        for (Invoke stmt : recv.getVar().getInvokes()) {
            JMethod method = resolveCallee(recvObj, stmt);  // 解析方法签名
            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            Context newContext = contextSelector.selectContext(csCallSite, recvObj, method);    // 确定被调方法的上下文

            // recv var -> this var
            CSVar csThisVar = csManager.getCSVar(newContext, method.getIR().getThis());
            addPFGEdge(recv, csThisVar);

            CSMethod csMethod = csManager.getCSMethod(newContext, method);
            Edge<CSCallSite, CSMethod> edge = new Edge<>(getCallKind(stmt), csCallSite, csMethod);   // 获得调用边
            if (callGraph.addEdge(edge)) {
                addReachable(csMethod);
                passArgsAndRetVar(stmt, method, context, newContext);
            }
        }
    }

    /**
     * 为函数调用传递参数和返回值
     * @param stmt
     * @param method
     * @param rawContext
     * @param newContext
     */
    private void passArgsAndRetVar(Invoke stmt, JMethod method, Context rawContext, Context newContext) {
        // args -> params
        for (int i = 0; i < method.getParamCount(); i++) {
            CSVar csArgVar = csManager.getCSVar(rawContext, stmt.getInvokeExp().getArg(i));
            CSVar csParamVar = csManager.getCSVar(newContext, method.getIR().getParam(i));
            addPFGEdge(csArgVar, csParamVar);
        }

        // 传递 ret var
        Var lVar = stmt.getLValue();
        if (lVar != null) {
            CSVar csLVar = csManager.getCSVar(rawContext, lVar);
            for (Var retVar : method.getIR().getReturnVars()) {
                CSVar csRetVar = csManager.getCSVar(newContext, retVar);
                addPFGEdge(csRetVar, csLVar);
            }
        }
    }

    /**
     * 获得调用函数的调用类型
     * @param stmt
     * @return
     */
    private CallKind getCallKind(Invoke stmt) {
        if (stmt.isInterface()) return CallKind.INTERFACE;
        if (stmt.isVirtual()) return CallKind.VIRTUAL;
        if (stmt.isSpecial()) return CallKind.SPECIAL;
        if (stmt.isStatic()) return CallKind.STATIC;
        if (stmt.isDynamic()) return CallKind.DYNAMIC;
        return CallKind.OTHER;
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
