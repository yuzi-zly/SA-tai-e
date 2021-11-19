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
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.lang.invoke.CallSite;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(HeapModel heapModel, ContextSelector contextSelector) {
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
        JMethod main = World.getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if(!callGraph.contains(csMethod)){
            callGraph.addReachableMethod(csMethod);
            for(Stmt stmt : csMethod.getMethod().getIR().getStmts()){
                if(stmt instanceof New){
                    CSVar csVar = csManager.getCSVar(csMethod.getContext(), ((New) stmt).getLValue());
                    CSObj csObj = csManager.getCSObj(csMethod.getContext(), heapModel.getObj((New) stmt));
                    PointsToSet pointsToSet = PointsToSetFactory.make(csObj);
                    workList.addEntry(csVar, pointsToSet);
                }
                else if(stmt instanceof Copy){
                    CSVar lCSVar = csManager.getCSVar(csMethod.getContext(), ((Copy) stmt).getLValue());
                    CSVar rCSVar = csManager.getCSVar(csMethod.getContext(), ((Copy) stmt).getRValue());
                    addPFGEdge(rCSVar, lCSVar);
                }
                else if(stmt instanceof LoadField){
                    if(((LoadField) stmt).isStatic()){
                        CSVar CSVar = csManager.getCSVar(csMethod.getContext(), ((LoadField) stmt).getLValue());
                        StaticField rPtr = csManager.getStaticField(((LoadField) stmt).getFieldRef().resolve());
                        addPFGEdge(rPtr, CSVar);
                    }
                }
                else if(stmt instanceof  StoreField){
                    if(((StoreField) stmt).isStatic()){
                        StaticField lPtr = csManager.getStaticField(((StoreField) stmt).getFieldRef().resolve());
                        CSVar csVar = csManager.getCSVar(csMethod.getContext(), ((StoreField) stmt).getRValue());
                        addPFGEdge(csVar, lPtr);
                    }
                }
                else if(stmt instanceof Invoke){
                    if(((Invoke) stmt).isStatic()){
                        //select Context
                        CSCallSite csCallSites = csManager.getCSCallSite(csMethod.getContext(), ((Invoke) stmt));
                        JMethod callee = resolveCallee(null, ((Invoke) stmt));
                        Context context = contextSelector.selectContext(csCallSites, callee);
                        //call edge
                        CSMethod csCallee = csManager.getCSMethod(context, callee);
                        Edge<CSCallSite, CSMethod> edge = new Edge<>(CallGraphs.getCallKind(((Invoke) stmt)), csCallSites, csCallee);
                        if(callGraph.addEdge(edge)){
                            addReachable(csCallee);
                            //args -> params
                            List<Var> args = ((Invoke) stmt).getInvokeExp().getArgs();
                            List<Var> params = callee.getIR().getParams();
                            for(int i = 0; i < args.size(); ++i){
                                CSVar argPtr = csManager.getCSVar(csMethod.getContext(), args.get(i));
                                CSVar parPtr = csManager.getCSVar(context, params.get(i));
                                addPFGEdge(argPtr, parPtr);
                            }
                            //return value
                            Var result = ((Invoke) stmt).getLValue();
                            if(result != null){
                                CSVar resultPtr = csManager.getCSVar(csMethod.getContext(), result);
                                List<Var> returnVars = callee.getIR().getReturnVars();
                                for(Var returnVar : returnVars){
                                    CSVar retPtr = csManager.getCSVar(context, returnVar);
                                    addPFGEdge(retPtr, resultPtr);
                                }
                            }
                        }
                    }
                }
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
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if(pointerFlowGraph.addEdge(source, target)){
            PointsToSet sourcePts = source.getPointsToSet();
            if(!sourcePts.isEmpty()){
                workList.addEntry(target, sourcePts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet delta = propagate(entry.pointer, entry.pointsToSet);
            if(entry.pointer instanceof CSVar) {
                Context context = ((CSVar) entry.pointer).getContext();
                for(CSObj csObj : delta){
                    Var var = ((CSVar) entry.pointer).getVar();
                    for(StoreField storeField : var.getStoreFields()){
                        InstanceField lPtr = csManager.getInstanceField(csObj, storeField.getFieldRef().resolve());
                        CSVar rPtr = csManager.getCSVar(context, storeField.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(LoadField loadField : var.getLoadFields()){
                        CSVar lPtr = csManager.getCSVar(context, loadField.getLValue());
                        InstanceField rPtr = csManager.getInstanceField(csObj, loadField.getFieldRef().resolve());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(StoreArray storeArray : var.getStoreArrays()){
                        ArrayIndex lPtr = csManager.getArrayIndex(csObj);
                        CSVar rPtr = csManager.getCSVar(context, storeArray.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(LoadArray loadArray : var.getLoadArrays()){
                        CSVar lPtr = csManager.getCSVar(context, loadArray.getLValue());
                        ArrayIndex rPtr = csManager.getArrayIndex(csObj);
                        addPFGEdge(rPtr, lPtr);
                    }
                    processCall(((CSVar)entry.pointer), csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = PointsToSetFactory.make();
        Set<CSObj> objSet = pointer.getPointsToSet().getObjects();
        for(CSObj csObj : pointsToSet){
            if(!objSet.contains(csObj)){
                delta.addObject(csObj);
            }
        }

        if(!delta.isEmpty()){
            for(CSObj csObj : delta){
                pointer.getPointsToSet().addObject(csObj);
            }

            pointerFlowGraph.succsOf(pointer).forEach(succ -> {
                workList.addEntry(succ, delta);
            });
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for(Invoke invoke : recv.getVar().getInvokes()){
            //disPatch
            JMethod callee = resolveCallee(recvObj, invoke);
            //select
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context context = contextSelector.selectContext(csCallSite, recvObj, callee);
            //this
            PointsToSet pointsToSet = PointsToSetFactory.make(recvObj);
            CSVar thisPtr = csManager.getCSVar(context, callee.getIR().getThis());
            workList.addEntry(thisPtr, pointsToSet);
            //call edge
            Edge<CSCallSite, CSMethod> edge = new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee);
            if(callGraph.addEdge(edge)){
                addReachable(callee);
                List<Var> args = invoke.getInvokeExp().getArgs();
                List<Var> params = callee.getIR().getParams();
                for(int i = 0; i < args.size(); ++i){
                    VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                    VarPtr parPtr = pointerFlowGraph.getVarPtr(params.get(i));
                    addPFGEdge(argPtr, parPtr);
                }

                Var result = invoke.getResult();
                if(result != null){
                    VarPtr resultPtr = pointerFlowGraph.getVarPtr(result);
                    List<Var> returnVars = callee.getIR().getReturnVars();
                    for(Var returnVar : returnVars){
                        VarPtr retPtr = pointerFlowGraph.getVarPtr(returnVar);
                        addPFGEdge(retPtr, resultPtr);
                    }
                }
            }
        }
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
