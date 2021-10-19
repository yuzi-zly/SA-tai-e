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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.IntraproceduralAnalysis;
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
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;
import java.util.stream.Collectors;

public class DeadCodeDetection extends IntraproceduralAnalysis {

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
        // Your task is to recognize dead code in ir and add it to deadCode
        traverseAndDetect(cfg, constants, liveVars, deadCode);
        return deadCode;
    }

    private static void traverseAndDetect(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants,
                                                 DataflowResult<Stmt, SetFact<Var>> liveVars, Set<Stmt> deadCode){
        Set<Stmt> meetCode = new HashSet<>();
        for(Stmt stmt : cfg){
            deadCode.add(stmt);
        }
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        while(!queue.isEmpty()){
            Stmt stmt = queue.poll();
            if(meetCode.contains(stmt))
                continue;

            if(stmt instanceof If){
                ConditionExp conditionExp = ((If) stmt).getCondition();
                Value value = ConstantPropagation.evaluate(conditionExp, constants.getInFact(stmt));
                if(value.isConstant()){
                    boolean conditionResult = value.getConstant() == 1;
                    List<Edge<Stmt>> edges = cfg.outEdgesOf(stmt).collect(Collectors.toList());
                    assert edges.size() == 2;
                    for(Edge<Stmt> edge : edges){
                        if(conditionResult && edge.getKind() == Edge.Kind.IF_TRUE){
                            meetCode.add(stmt);
                            deadCode.remove(stmt);
                            queue.add(edge.getTarget());
                        }
                        else if(!conditionResult && edge.getKind() == Edge.Kind.IF_FALSE){
                            meetCode.add(stmt);
                            deadCode.remove(stmt);
                            queue.add(edge.getTarget());
                        }
                    }
                }
                else{
                    meetCode.add(stmt);
                    deadCode.remove(stmt);
                    cfg.outEdgesOf(stmt).forEach(edge -> {
                        queue.add(edge.getTarget());
                    });
                }
            }
            else if(stmt instanceof SwitchStmt){
                Var var = ((SwitchStmt) stmt).getVar();
                Value value = ConstantPropagation.evaluate(var, constants.getInFact(stmt));
                if(value.isConstant()){
                    int val = value.getConstant();
                    List<Pair<Integer, Stmt>> caseTargets = ((SwitchStmt) stmt).getCaseTargets();
                    boolean toDefault = true;
                    for(Pair<Integer, Stmt> caseTarget : caseTargets){
                        if(caseTarget.getFirst() == val){
                            toDefault = false;
                            meetCode.add(stmt);
                            deadCode.remove(stmt);
                            queue.add(caseTarget.getSecond());
                            break;
                        }
                    }
                    if(toDefault){
                        meetCode.add(stmt);
                        deadCode.remove(stmt);
                        queue.add(((SwitchStmt) stmt).getDefaultTarget());
                    }

                }
                else{
                    meetCode.add(stmt);
                    deadCode.remove(stmt);
                    cfg.outEdgesOf(stmt).forEach(edge -> {
                        queue.add(edge.getTarget());
                    });
                }
            }
            else if(stmt instanceof AssignStmt) {
                RValue rValue = ((AssignStmt<?,?>) stmt).getRValue();
                if(hasNoSideEffect(rValue)){
                    LValue var = ((AssignStmt<?,?>) stmt).getLValue();
                    assert var instanceof Var;
                    SetFact<Var> setFact = liveVars.getOutFact(stmt);
                    meetCode.add(stmt);
                    if(setFact.contains((Var) var)){
                        //live
                        deadCode.remove(stmt);
                    }
                    cfg.outEdgesOf(stmt).forEach(edge -> {
                        queue.add(edge.getTarget());
                    });
                }
                else{
                    meetCode.add(stmt);
                    deadCode.remove(stmt);
                    cfg.outEdgesOf(stmt).forEach(edge -> {
                        queue.add(edge.getTarget());
                    });
                }
            }
            else {
                meetCode.add(stmt);
                deadCode.remove(stmt);
                cfg.outEdgesOf(stmt).forEach(edge -> {
                    queue.add(edge.getTarget());
                });
            }
        }
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
}
