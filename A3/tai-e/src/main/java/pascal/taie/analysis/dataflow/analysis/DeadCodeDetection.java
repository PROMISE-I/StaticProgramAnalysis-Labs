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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        traversalCFGDeadCode(deadCode, cfg, constants, liveVars);
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }

    enum Color {
        White, Gray, Black
    }

    private void traversalCFGDeadCode(Set<Stmt> deadCode, CFG<Stmt> cfg,
                                      DataflowResult<Stmt, CPFact> constants,
                                      DataflowResult<Stmt, SetFact<Var>> liveVars) {
        // initialize Color information for every node in cfg which is stmt.
        Map<Stmt, Color> traverColorInfo = new HashMap<>();
        for (Stmt stmt : cfg) {
            traverColorInfo.put(stmt, Color.White);
        }

        for(Stmt stmt : traverColorInfo.keySet()) {
            if (cfg.isEntry(stmt) && traverColorInfo.get(stmt) == Color.White) {
                dfsCFGDeadCode(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
            }
        }

        addUnreachableStmt(cfg, deadCode, traverColorInfo);
    }

    private void dfsCFGDeadCode(Stmt stmt, Map<Stmt, Color> traverColorInfo, Set<Stmt> deadCode,
                                CFG<Stmt> cfg,
                                DataflowResult<Stmt, CPFact> constants,
                                DataflowResult<Stmt, SetFact<Var>> liveVars) {
        traverColorInfo.put(stmt, Color.Gray);

        if (stmt instanceof Invoke || stmt instanceof AssignStmt<?,?>) {
            if (stmt instanceof Invoke) handleInvoke((Invoke) stmt, deadCode, liveVars);
            else handleAssign((AssignStmt<?, ?>) stmt, deadCode, liveVars);

            traversalAllSuccessor(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
        else if (stmt instanceof If) {
            handleIf(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
        else if (stmt instanceof SwitchStmt) {
            handleSwitch(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
        else {
            traversalAllSuccessor(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }

        traverColorInfo.put(stmt, Color.Black);
    }

    private void handleInvoke(Invoke stmt, Set<Stmt> deadCode,
                              DataflowResult<Stmt, SetFact<Var>> liveVars) {
        LValue lValue = stmt.getLValue();
        if (lValue instanceof Var lv) {
            SetFact<Var> outFact = liveVars.getOutFact(stmt);
            if (!outFact.contains(lv)) {
                // lv is not livable
                if (hasNoSideEffect(((Invoke) stmt).getRValue())) {
                    deadCode.add(stmt);
                }
            }
        }
    }

    private void handleAssign(AssignStmt<?,?> stmt, Set<Stmt> deadCode,
                              DataflowResult<Stmt, SetFact<Var>> liveVars) {
        LValue lValue = stmt.getLValue();
        if (lValue instanceof Var lv) {
            SetFact<Var> outFact = liveVars.getOutFact(stmt);
            if (!outFact.contains(lv)) {
                // lv is not livable
                deadCode.add(stmt);
            }
        }
    }

    private void handleIf(Stmt stmt, Map<Stmt, Color> traverColorInfo, Set<Stmt> deadCode,
                          CFG<Stmt> cfg,
                          DataflowResult<Stmt, CPFact> constants,
                          DataflowResult<Stmt, SetFact<Var>> liveVars) {
        CPFact inFact = constants.getInFact(stmt);
        ConditionExp condition = ((If) stmt).getCondition();

        Value condVal = ConstantPropagation.evaluate(condition, inFact);
        if (condVal.isConstant()) {
            for (Edge<Stmt> e: cfg.getOutEdgesOf(stmt)) {
                if ((condVal.getConstant() == 0 && e.getKind() == Edge.Kind.IF_FALSE) ||
                    (condVal.getConstant() == 1 && e.getKind() == Edge.Kind.IF_TRUE)) {
                    Stmt succ = e.getTarget();
                    traversalSpecificStmt(succ, traverColorInfo, deadCode, cfg, constants, liveVars);
                    break;
                }
            }
        } else {
            // normal traversal
            traversalAllSuccessor(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
    }

    private void handleSwitch(Stmt stmt, Map<Stmt, Color> traverColorInfo, Set<Stmt> deadCode,
                              CFG<Stmt> cfg,
                              DataflowResult<Stmt, CPFact> constants,
                              DataflowResult<Stmt, SetFact<Var>> liveVars) {
        CPFact inFact = constants.getInFact(stmt);
        Var var = ((SwitchStmt) stmt).getVar();

        Value varValue = ConstantPropagation.evaluate(var, inFact);
        if (varValue.isConstant()) {
            boolean isDefault = true;

            for (Pair<Integer, Stmt> p : ((SwitchStmt) stmt).getCaseTargets()) {
                if (varValue.getConstant() == p.first()) {
                    isDefault = false;

                    Stmt succ = p.second();
                    traversalSpecificStmt(succ, traverColorInfo, deadCode, cfg, constants, liveVars);
                }
            }

            if (isDefault) {
                Stmt succ = ((SwitchStmt) stmt).getDefaultTarget();
                traversalSpecificStmt(succ, traverColorInfo, deadCode, cfg, constants, liveVars);
            }
        } else {
            // normal traversal
            traversalAllSuccessor(stmt, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
    }

    private void traversalAllSuccessor(Stmt stmt, Map<Stmt, Color> traverColorInfo, Set<Stmt> deadCode,
                                       CFG<Stmt> cfg,
                                       DataflowResult<Stmt, CPFact> constants,
                                       DataflowResult<Stmt, SetFact<Var>> liveVars) {
        for (Stmt succ : cfg.getSuccsOf(stmt)) {
            traversalSpecificStmt(succ, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
    }

    private void traversalSpecificStmt(Stmt successor, Map<Stmt, Color> traverColorInfo, Set<Stmt> deadCode,
                                       CFG<Stmt> cfg,
                                       DataflowResult<Stmt, CPFact> constants,
                                       DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (traverColorInfo.get(successor) == Color.White) {
            dfsCFGDeadCode(successor, traverColorInfo, deadCode, cfg, constants, liveVars);
        }
    }

    private void addUnreachableStmt(CFG<Stmt> cfg, Set<Stmt> deadCode, Map<Stmt, Color> traverColorInfo) {
        for (Stmt stmt : traverColorInfo.keySet()) {
            if (!cfg.isExit(stmt) && traverColorInfo.get(stmt) == Color.White) {
                deadCode.add(stmt);
            }
        }
    }

}
