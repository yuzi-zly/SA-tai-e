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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.LinkedList;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<>();
        for(Node node : cfg){
            workList.add(node);
        }
        while(!workList.isEmpty()){
            Node node = workList.poll();
            cfg.predsOf(node).forEach(pred -> {
                analysis.meetInto(result.getOutFact(pred), result.getInFact(node));
            });

            boolean chgOccur = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(chgOccur){
                cfg.succsOf(node).forEach(succ ->{
                    workList.add(succ);
                });
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new LinkedList<>();
        for(Node node : cfg){
            workList.add(node);
        }
        while(!workList.isEmpty()){
            Node node = workList.poll();
            cfg.succsOf(node).forEach(succ -> {
                analysis.meetInto(result.getInFact(succ), result.getOutFact(node));
            });

            boolean chgOccur = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(chgOccur){
                cfg.predsOf(node).forEach(pred -> {
                    workList.add(pred);
                });
            }
        }
    }
}
