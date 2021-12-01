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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    public DataflowResult<Node, Fact> getResult() {
        return result;
    }

    private void initialize() {
        List<Method> entryList = icfg.entryMethods().collect(Collectors.toList());
        assert entryList.size() == 1;
        Node entryNode = icfg.getEntryOf(entryList.get(0));
        result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        result.setInFact(entryNode, analysis.newInitialFact());
        for(Node node : icfg){
            if(node.equals(entryNode)) continue;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        workList = new LinkedList<>();
        fillWorkList();
        while(!workList.isEmpty()){
            Node node = workList.poll();
            System.out.println("InterSolver: " + node);
            icfg.inEdgesOf(node).forEach(nodeICFGEdge -> {
                Node pred = nodeICFGEdge.getSource();
                Fact fact = analysis.transferEdge(nodeICFGEdge, result.getOutFact(pred));
                analysis.meetInto(fact, result.getInFact(node));
            });

            boolean chgOccur = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));
            if(chgOccur){
                icfg.outEdgesOf(node).forEach(nodeICFGEdge -> {
                    workList.add(nodeICFGEdge.getTarget());
                });
            }
        }
    }

    //按照调用顺序添加
    private void fillWorkList(){
        List<Method> entryList = icfg.entryMethods().collect(Collectors.toList());
        assert entryList.size() == 1;
        Stack<Node> stack = new Stack<>();
        stack.add(icfg.getEntryOf(entryList.get(0)));
        while(!stack.isEmpty()){
            Node tempNode = stack.pop();
            if(workList.contains(tempNode))
                continue;
            workList.add(tempNode);
            icfg.outEdgesOf(tempNode).forEach(nodeICFGEdge -> {
                Node succ = nodeICFGEdge.getTarget();
                stack.add(succ);
            });
        }
        for(Node node : icfg){
            if(workList.contains(node))
                continue;
            workList.add(node);
        }
    }


}
