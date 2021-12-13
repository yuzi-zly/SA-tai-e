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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.getClassHierarchy(),
                World.getTypeManager());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        List<CSMethod> reachableMethods = callGraph.reachableMethods().collect(Collectors.toList());
        //遍历所有的callSite判断是否是sink
        for(CSMethod csMethod : reachableMethods){
            List<CSCallSite> csCallSites = callGraph.callSitesIn(csMethod).collect(Collectors.toList());
            for(CSCallSite csCallSite : csCallSites){
                int argSize = csCallSite.getCallSite().getInvokeExp().getArgCount();
                for(int i = 0; i < argSize; ++i){
                    if(isSink(csCallSite.getCallSite(), i)){
                        Var arg = csCallSite.getCallSite().getInvokeExp().getArg(i);
                        CSVar argPtr = csManager.getCSVar(csCallSite.getContext(), arg);
                        for(CSObj csObj : argPtr.getPointsToSet()){ //遍历指向的所有对象
                            if(manager.isTaint(csObj.getObject())){ //是一个Taint obj
                                Invoke source = manager.getSourceCall(csObj.getObject());
                                Invoke sink = csCallSite.getCallSite();
                                taintFlows.add(new TaintFlow(source, sink, i));
                            }
                        }
                    }
                }
            }
        }
        // You could query pointer analysis results you need via variable result.
        return taintFlows;
    }

    public Context getEmptyContext() {
        return emptyContext;
    }

    //For Source
    public Obj sourceMatch(Invoke invoke){
        JMethod invokeMethod = invoke.getMethodRef().resolve();
        Source source = new Source(invokeMethod, invokeMethod.getReturnType());
        for(Source source1 : config.getSources()){
            if(source.equals(source1)){
                return manager.makeTaint(invoke, invokeMethod.getReturnType());
            }
        }
        return null;
    }

    //For Sink
    private boolean isSink(Invoke invoke, int argIndex){
        JMethod invokeMethod = invoke.getMethodRef().resolve();
        Sink sink = new Sink(invokeMethod, argIndex);
        for(Sink sink1 : config.getSinks()){
            if(sink.equals(sink1)){
                return true;
            }
        }
        return false;
    }

    //For Transfer
    public boolean isA2RTransfer(Invoke invoke, int argIndex){
        JMethod invokeMethod = invoke.getMethodRef().resolve();
        TaintTransfer taintTransfer = new TaintTransfer(
                invokeMethod, argIndex, TaintTransfer.RESULT, invokeMethod.getReturnType()
        );
        for(TaintTransfer taintTransfer1 : config.getTransfers()){
            if (taintTransfer.equals(taintTransfer1)) {
                return true;
            }
        }
        return false;
    }

    public boolean isB2RTransfer(Invoke invoke){
        JMethod invokeMethod = invoke.getMethodRef().resolve();
        TaintTransfer taintTransfer = new TaintTransfer(
            invokeMethod, TaintTransfer.BASE, TaintTransfer.RESULT, invokeMethod.getReturnType()
        );
        for(TaintTransfer taintTransfer1 : config.getTransfers()){
            if(taintTransfer.equals(taintTransfer1)){
                return true;
            }
        }
        return false;
    }

    public boolean isA2BTransfer(Invoke invoke, int argIndex){
        JMethod invokeMethod = invoke.getMethodRef().resolve();
        TaintTransfer taintTransfer = new TaintTransfer(
                invokeMethod, argIndex, TaintTransfer.BASE, invokeMethod.getReturnType()
        );
        for(TaintTransfer taintTransfer1 : config.getTransfers()){
            if (taintTransfer.equals(taintTransfer1)) {
                return true;
            }
        }
        return false;
    }

    public Obj taintObjTransfer(Obj oldObj, Type type){
        if(manager.isTaint(oldObj)){
            Invoke source = manager.getSourceCall(oldObj);
            return manager.makeTaint(source, type);
        }
        return null;
    }

}
