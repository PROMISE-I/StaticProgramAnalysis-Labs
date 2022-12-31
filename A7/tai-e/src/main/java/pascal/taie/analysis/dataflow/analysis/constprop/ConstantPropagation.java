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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();

        List<Var> vars = cfg.getIR().getParams();
        for(Var v : vars) {
            if (canHoldInt(v)) {
                fact.update(v, Value.getNAC());
            }
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for (Var varOrigin : fact.keySet()) {
            Value valueOrigin = fact.get(varOrigin);
            Value valueTarget = target.get(varOrigin);

            Value valueFinal = meetValue(valueOrigin, valueTarget);
            target.update(varOrigin, valueFinal);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isUndef()) { // question: 引用传递在这里不会出错嘛？是因为forward 变了success就一定会改变是吗？
            return v1;
        } else if (v2.isNAC() || v1.isUndef()) {
            return v2;
        } else if (v1.equals(v2)){
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact outOrigin = out.copy();
        out.clear();
        for (Var v : in.keySet()) {
            out.update(v, in.get(v));
        }

        if (stmt instanceof DefinitionStmt<?,?>) {
            LValue lv = ((DefinitionStmt<?, ?>) stmt).getLValue();
            RValue rv = ((DefinitionStmt<?, ?>) stmt).getRValue();

            if (lv instanceof Var && canHoldInt((Var)lv)) {
                Value val = evaluate(rv, in);
                out.update((Var)lv, val);
            }
        }

        return !outOrigin.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var) {
            return evalVar(exp, in);
        } else if (exp instanceof IntLiteral) {
            return evalIntLiteral(exp);
        } else if (exp instanceof BinaryExp) {
            return evalBinaryExp(exp, in);
        } else {
            //other cases for example: method invoke && field load
            return Value.getNAC();
        }
    }

    private static Value evalVar(Exp exp, CPFact in) {
        Var v = (Var) exp;
        return in.get(v);
    }

    private static Value evalIntLiteral(Exp exp) {
        int val = ((IntLiteral) exp).getValue();
        return Value.makeConstant(val);
    }

    private static Value evalBinaryExp(Exp exp, CPFact in) {
        // BinaryExp
        BinaryExp be = (BinaryExp) exp;

        BinaryExp.Op operator = be.getOperator();
        Var op1 = be.getOperand1();
        Value val1 = in.get(op1);
        Var op2 = be.getOperand2();
        Value val2 = in.get(op2);

        Value resValue = handleDivideByZero(operator.toString(), val2);
        if (resValue != null) return resValue;

        if (val1.isConstant() && val2.isConstant()) {
            int value1 = val1.getConstant();
            int value2 = val2.getConstant();
            return calculate(value1, value2, operator.toString());
        }

        if (val1.isNAC() || val2.isNAC()){
            return Value.getNAC();
        }

        return Value.getUndef();
    }

    private static Value calculate(int value1, int value2, String operator) {
        switch (operator) {
            // ArithmeticExp
            case "+":
                return Value.makeConstant(value1 + value2);
            case "-":
                return Value.makeConstant(value1 - value2);
            case "*":
                return Value.makeConstant(value1 * value2);
            case "/":
                return Value.makeConstant(value1 / value2);
            case "%":
                return Value.makeConstant(value1 % value2);
            // BitwiseExp
            case "|":
                return Value.makeConstant(value1 | value2);
            case "&":
                return Value.makeConstant(value1 & value2);
            case "^":
                return Value.makeConstant(value1 ^ value2);
            //ConditionExp
            case "==":
                if (value1 == value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
            case "!=":
                if (value1 != value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
            case "<":
                if (value1 < value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
            case ">":
                if (value1 > value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
            case "<=":
                if (value1 <= value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
            case ">=":
                if (value1 >= value2) return Value.makeConstant(1);
                else return Value.makeConstant(0);
                //ShiftExp
            case "<<":
                return Value.makeConstant(value1 << value2);
            case ">>":
                return Value.makeConstant(value1 >> value2);
            case ">>>":
                return Value.makeConstant(value1 >>> value2);
            default:
                throw new RuntimeException("Unknown operator: " + operator);
        }
    }

    private static Value handleDivideByZero(String operator, Value divider) {
        switch (operator) {
            case "/":
            case "%":
                if (divider.isConstant() && divider.getConstant() == 0) {
                    return Value.getUndef();
                }
            default:
                return null;
        }
    }
}

