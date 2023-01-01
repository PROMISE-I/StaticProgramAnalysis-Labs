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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final Map<LoadField, Set<StoreField>> loadStoreFieldMap = new HashMap<>();

    private final Map<StoreField, Set<LoadField>> storeLoadFieldMap = new HashMap<>();

    private final Map<LoadArray, Set<StoreArray>> loadStoreArrayMap = new HashMap<>();

    private final Map<StoreArray, Set<LoadArray>> storeLoadArrayMap = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        for (Stmt stmt : icfg.getNodes()) {
            if (stmt instanceof LoadField loadFieldStmt) {
                loadStoreFieldMap.put(loadFieldStmt, new HashSet<>());
            }
            if (stmt instanceof StoreField storeFieldStmt) {
                storeLoadFieldMap.put(storeFieldStmt, new HashSet<>());
            }
            if (stmt instanceof LoadArray loadArrayStmt) {
                loadStoreArrayMap.put(loadArrayStmt, new HashSet<>());
            }
            if (stmt instanceof StoreArray storeArrayStmt) {
                storeLoadArrayMap.put(storeArrayStmt, new HashSet<>());
            }
        }

        for (Stmt stmt : icfg.getNodes()) {
            if (stmt instanceof LoadField loadFieldStmt) {
                fillFieldMap(loadFieldStmt, pta);
            } else if (stmt instanceof LoadArray loadArrayStmt) {
                fillArrayMap(loadArrayStmt, pta);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact outOrigin = out.copy();
        out.clear();
        for (Var v : in.keySet()) {
            out.update(v, in.get(v));
        }
        return !outOrigin.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact outOrigin = out.copy();
        out.clear();
        for (Var v : in.keySet()) {
            out.update(v, in.get(v));
        }

        if (stmt instanceof LoadField loadFieldStmt) {
            /* x = y.f || x = T.f */
            Var lValue = loadFieldStmt.getLValue();
            out.update(lValue, Value.getUndef());

            if (ConstantPropagation.canHoldInt(lValue)) {
                transferLoadField(loadFieldStmt, out, lValue);
            }
        } else if (stmt instanceof StoreField storeFieldStmt && !outOrigin.equals(out)) {
            /* y.f = x || T.f = x */
            for (LoadField loadFieldStmt : storeLoadFieldMap.get(storeFieldStmt)) {
                solver.addNodeToWorkList(loadFieldStmt);
            }
        } else if (stmt instanceof LoadArray loadArrayStmt) {
            /* x = a[i] */
            Var lValue = loadArrayStmt.getLValue();
            out.update(lValue, Value.getUndef());

            if (ConstantPropagation.canHoldInt(lValue)) {
                transferLoadArray(loadArrayStmt, in, out, lValue);
            }
        } else if (stmt instanceof StoreArray storeArrayStmt && !outOrigin.equals(out)) {
            /* a[i] = x */
            for (LoadArray loadArrayStmt : storeLoadArrayMap.get(storeArrayStmt)) {
                solver.addNodeToWorkList(loadArrayStmt);
            }
        } else if (stmt instanceof DefinitionStmt<?,?> definitionStmt) {
            LValue lv = definitionStmt.getLValue();
            RValue rv = definitionStmt.getRValue();

            if (lv instanceof Var && ConstantPropagation.canHoldInt((Var)lv)) {
                Value val = ConstantPropagation.evaluate(rv, in);
                out.update((Var)lv, val);
            }
        }

        return !outOrigin.equals(out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact outWithoutLV = out.copy();
        Stmt stmt = edge.getSource();

        if (stmt instanceof DefinitionStmt<?,?>) {
            LValue lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lv instanceof Var returnVar && ConstantPropagation.canHoldInt((Var) lv)) {
                outWithoutLV.update(returnVar, Value.getUndef());
            }
        }

        return outWithoutLV;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt sourceStmt = edge.getSource();
        InvokeExp invokeExp = ((Invoke) sourceStmt).getInvokeExp();

        CPFact calleeInFact = new CPFact();
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            Var param = edge.getCallee().getIR().getParam(i);
            Var arg = invokeExp.getArg(i);

            calleeInFact.update(param, callSiteOut.get(arg));
        }

        return calleeInFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact calleeOutFact = new CPFact();

        Stmt callSiteStmt = edge.getCallSite();
        if (callSiteStmt instanceof DefinitionStmt<?,?>) {
            LValue lv = ((DefinitionStmt<?, ?>) callSiteStmt).getLValue();
            if (lv instanceof Var returnVar && ConstantPropagation.canHoldInt((Var) lv)) {
                Value returnValue = Value.getUndef();

                for (Var rv : edge.getReturnVars()) {
                    returnValue = cp.meetValue(returnValue, returnOut.get(rv));
                }

                calleeOutFact.update(returnVar, returnValue);
            }
        }

        return calleeOutFact;
    }

    private void fillFieldMap(LoadField loadFieldStmt, PointerAnalysisResult pta) {
        Var lValue = loadFieldStmt.getLValue();
        if (ConstantPropagation.canHoldInt(lValue)) {
            if (!loadFieldStmt.isStatic()) {
                Var base = ((InstanceFieldAccess)(loadFieldStmt.getFieldAccess())).getBase();
                JField originField = loadFieldStmt.getFieldRef().resolve();

                Set<Obj> basePTS = pta.getPointsToSet(base);
                for (Var v : pta.getVars()) {
                    Set<Obj> vPTS = new HashSet<>(pta.getPointsToSet(v));
                    if (vPTS.removeAll(basePTS)) {
                        for (StoreField storeFieldStmt : v.getStoreFields()) {
                            checkJFieldAndFillFieldMap(loadFieldStmt, storeFieldStmt, originField);
                        }
                    }
                }
            } else {
                JField originField = loadFieldStmt.getFieldRef().resolve();
                for (Stmt otherStmt : icfg.getNodes()) {
                    if (otherStmt instanceof StoreField storeFieldStmt && storeFieldStmt.isStatic()) {
                        checkJFieldAndFillFieldMap(loadFieldStmt, storeFieldStmt, originField);
                    }
                }
            }
        }
    }

    private void checkJFieldAndFillFieldMap(LoadField loadFieldStmt, StoreField storeFieldStmt, JField originField) {
        Var rValue = storeFieldStmt.getRValue();
        JField targetField = storeFieldStmt.getFieldRef().resolve();
        if (targetField.equals(originField) && ConstantPropagation.canHoldInt(rValue)) {
            loadStoreFieldMap.get(loadFieldStmt).add(storeFieldStmt);
            storeLoadFieldMap.get(storeFieldStmt).add(loadFieldStmt);
        }
    }

    private void fillArrayMap(LoadArray loadArrayStmt, PointerAnalysisResult pta) {
        Var lValue = loadArrayStmt.getLValue();
        if (ConstantPropagation.canHoldInt(lValue)) {
            Var base = loadArrayStmt.getArrayAccess().getBase();
            Set<Obj> basePTS = pta.getPointsToSet(base);
            for (Var v : pta.getVars()) {
                Set<Obj> vPTS = new HashSet<>(pta.getPointsToSet(v));
                if (vPTS.removeAll(basePTS)) {
                    for (StoreArray storeArrayStmt : v.getStoreArrays()) {
                        Var rValue = storeArrayStmt.getRValue();
                        if (ConstantPropagation.canHoldInt(rValue)) {
                            loadStoreArrayMap.get(loadArrayStmt).add(storeArrayStmt);
                            storeLoadArrayMap.get(storeArrayStmt).add(loadArrayStmt);
                        }
                    }
                }
            }
        }
    }

    private void transferLoadField(LoadField loadFieldStmt, CPFact out, Var lValue) {
        /* y = x.f */
        /* z = T.f */
        for (StoreField storeFieldStmt : loadStoreFieldMap.get(loadFieldStmt)) {
            Var rValue = storeFieldStmt.getRValue();
            Value newValue = cp.meetValue(out.get(lValue), solver.getInFact(storeFieldStmt).get(rValue));
            out.update(lValue, newValue);
        }
    }

    private void transferLoadArray(LoadArray loadArrayStmt, CPFact in, CPFact out, Var lValue) {
        /* x = a[i] */
        Var index = loadArrayStmt.getArrayAccess().getIndex();
        for (StoreArray storeArrayStmt : loadStoreArrayMap.get(loadArrayStmt)) {
            Var rValue = storeArrayStmt.getRValue();
            Var aliasIndex = storeArrayStmt.getArrayAccess().getIndex();
            // check index
            if (isAliasIndex(in.get(index), solver.getInFact(storeArrayStmt).get(aliasIndex))) {
                Value newValue = cp.meetValue(out.get(lValue), solver.getInFact(storeArrayStmt).get(rValue));
                out.update(lValue, newValue);
            }
        }
    }

    private boolean isAliasIndex(Value v1, Value v2) {
        if (v1.isUndef() || v2.isUndef()) {
            return false;
        } else return !v1.isConstant() || !v2.isConstant() || v1.equals(v2);
    }
}
