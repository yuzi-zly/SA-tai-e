/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2020-- Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2020-- Yue Li <yueli@nju.edu.cn>
 * All rights reserved.
 *
 * Tai-e is only for educational and academic purposes,
 * and any form of commercial use is disallowed.
 * Distribution of Tai-e is disallowed without the approval.
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

import java.util.Base64;
import java.util.List;
import java.util.Set;

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
        CPFact cpFact = new CPFact();
        for(Var param : cfg.getIR().getParams()){
            if(canHoldInt(param)){
                cpFact.update(param, Value.getNAC());
            }
        }
        return cpFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for(Var var : fact.keySet()){
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        else if(v1.isConstant() && v2.isConstant()){
            return v1.getConstant() == v2.getConstant() ? v1 : Value.getNAC();
        }
        else if(v1.isUndef() || v2.isUndef()){
            return v1.isUndef() ? v2 : v1;
        }
        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if(stmt instanceof DefinitionStmt){
            LValue var = ((DefinitionStmt<?,?>) stmt).getLValue();
            RValue exp = ((DefinitionStmt<?,?>) stmt).getRValue();
            if(!(var instanceof Var)){
                return out.copyFrom(in);
            }

            if(!canHoldInt(((Var) var))){
                // Type is not int
                return out.copyFrom(in);
            }

            Value gen = evaluate(exp, in);
            CPFact result = in.copy();
            result.remove((Var) var);
            result.update((Var) var, gen);
            return out.copyFrom(result);
        }
        else {
            return out.copyFrom(in);
        }
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
        if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        else if(exp instanceof Var){
            if(!canHoldInt((Var) exp)){
                return Value.getNAC();
            }
            return in.get(((Var) exp));
        }
        else if(exp instanceof BinaryExp){
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();

            if(!canHoldInt(operand1) || !canHoldInt(operand2)){
                return Value.getNAC();
            }

            if(in.get(operand1).isNAC() || in.get(operand2).isNAC()){
                if(exp instanceof ArithmeticExp && in.get(operand2).isConstant()){
                    ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
                    int val2 = in.get(operand2).getConstant();
                    if((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) && val2 == 0){
                        return Value.getUndef();
                    }
                }
                return Value.getNAC();
            }
            else if(!in.get(operand1).isConstant() || !in.get(operand2).isConstant()){
                return Value.getUndef();
            }
            else{
                if(exp instanceof ArithmeticExp){
                    ArithmeticExp.Op op = ((ArithmeticExp) exp).getOperator();
                    int val1 = in.get(operand1).getConstant();
                    int val2 = in.get(operand2).getConstant();
                    switch (op){
                        case ADD: return Value.makeConstant(val1 + val2);
                        case SUB: return Value.makeConstant(val1 - val2);
                        case MUL: return Value.makeConstant(val1 * val2);
                        case DIV: return val2 == 0 ? Value.getUndef() : Value.makeConstant(val1 / val2);
                        case REM: return val2 == 0 ? Value.getUndef() : Value.makeConstant(val1 % val2);
                        default: assert false;
                    }
                }
                else if(exp instanceof BitwiseExp){
                    BitwiseExp.Op op = ((BitwiseExp) exp).getOperator();
                    int val1 = in.get(operand1).getConstant();
                    int val2 = in.get(operand2).getConstant();
                    switch (op){
                        case AND: return Value.makeConstant(val1 & val2);
                        case OR: return Value.makeConstant(val1 | val2);
                        case XOR: return Value.makeConstant(val1 ^ val2);
                        default: assert false;
                    }
                }
                else if(exp instanceof ConditionExp){
                    ConditionExp.Op op = ((ConditionExp) exp).getOperator();
                    int val1 = in.get(operand1).getConstant();
                    int val2 = in.get(operand2).getConstant();
                    switch (op){
                        case EQ: return val1 == val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GE: return val1 >= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GT: return val1 >  val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LE: return val1 <= val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LT: return val1 <  val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        case NE: return val1 != val2 ? Value.makeConstant(1) : Value.makeConstant(0);
                        default: assert false;
                    }
                }
                else if(exp instanceof ShiftExp){
                    ShiftExp.Op op = ((ShiftExp) exp).getOperator();
                    int val1 = in.get(operand1).getConstant();
                    int val2 = in.get(operand2).getConstant();
                    switch (op){
                        case SHL: return Value.makeConstant(val1 << val2);
                        case SHR: return Value.makeConstant(val1 >> val2);
                        case USHR: return Value.makeConstant(val1 >>> val2);
                        default: assert false;
                    }
                }
            }
        }
        return Value.getNAC();
    }
}
