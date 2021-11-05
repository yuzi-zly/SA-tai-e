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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.getClassHierarchy();
        // initialize main method
        JMethod main = World.getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for(Stmt stmt : method.getIR().getStmts()){
                if(stmt instanceof New){
                    VarPtr varPtr = pointerFlowGraph.getVarPtr(((New) stmt).getLValue());
                    Obj obj = heapModel.getObj((New) stmt);
                    PointsToSet pointsToSet = new PointsToSet(obj);
                    workList.addEntry(varPtr, pointsToSet);
                }
                else if(stmt instanceof Copy){
                    VarPtr lPtr = pointerFlowGraph.getVarPtr(((Copy) stmt).getLValue());
                    VarPtr rPtr = pointerFlowGraph.getVarPtr(((Copy) stmt).getRValue());
                    addPFGEdge(rPtr, lPtr);
                }
                else if(stmt instanceof LoadField){
                    if(((LoadField) stmt).isStatic()){
                        VarPtr lPtr = pointerFlowGraph.getVarPtr(((LoadField) stmt).getLValue());
                        StaticField rPtr = pointerFlowGraph.getStaticField(((LoadField) stmt).getFieldRef().resolve());
                        addPFGEdge(rPtr, lPtr);
                    }
                }
                else if(stmt instanceof  StoreField){
                    if(((StoreField) stmt).isStatic()){
                        StaticField lPtr = pointerFlowGraph.getStaticField(((StoreField) stmt).getFieldRef().resolve());
                        VarPtr rPtr = pointerFlowGraph.getVarPtr(((StoreField) stmt).getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                }
                else if(stmt instanceof Invoke){
                    if(((Invoke) stmt).isStatic()){
                        Var result = ((Invoke) stmt).getLValue();
                        List<Var> args = ((Invoke) stmt).getInvokeExp().getArgs();
                        JMethod callee = resolveCallee(null, ((Invoke) stmt));
                        Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(((Invoke) stmt)), ((Invoke) stmt), callee);
                        if(callGraph.addEdge(edge)){
                            addReachable(callee);
                            List<Var> params = callee.getIR().getParams();
                            for(int i = 0; i < args.size(); ++i){
                                VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
                                VarPtr parPtr = pointerFlowGraph.getVarPtr(params.get(i));
                                addPFGEdge(argPtr, parPtr);
                            }
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
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
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
            if(entry.pointer instanceof VarPtr){
                for(Obj obj : delta){
                    Var var = ((VarPtr) entry.pointer).getVar();
                    for(StoreField storeField : var.getStoreFields()){
                        InstanceField lPtr = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        VarPtr rPtr = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(LoadField loadField : var.getLoadFields()){
                        VarPtr lPtr = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        InstanceField rPtr = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(StoreArray storeArray : var.getStoreArrays()){
                        ArrayIndex lPtr = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr rPtr = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(rPtr, lPtr);
                    }
                    for(LoadArray loadArray : var.getLoadArrays()){
                        VarPtr lPtr = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        ArrayIndex rPtr = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(rPtr, lPtr);
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet delta = new PointsToSet();
        Set<Obj> objSet = pointer.getPointsToSet().getObjects();
        for(Obj obj : pointsToSet){
            if(!objSet.contains(obj)){
                delta.addObject(obj);
            }
        }

        if(!delta.isEmpty()){
            for(Obj obj : delta){
                pointer.getPointsToSet().addObject(obj);
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for(Invoke invoke : var.getInvokes()){
            JMethod callee = resolveCallee(recv, invoke);
            PointsToSet pointsToSet = new PointsToSet(recv);
            VarPtr thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(thisPtr, pointsToSet);

            Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee);
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
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
