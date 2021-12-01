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

 import pascal.taie.World;
 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.graph.callgraph.CallGraph;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.analysis.pta.PointerAnalysisResult;
 import pascal.taie.analysis.pta.core.heap.Obj;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.*;
 import pascal.taie.ir.stmt.*;
 import pascal.taie.language.classes.JField;
 import pascal.taie.language.classes.JMethod;

 import java.util.List;
 import java.util.Set;
 import java.util.stream.Collectors;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;

     public PointerAnalysisResult pta;

     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
     }

     @Override
     protected void initialize() {
         String ptaId = getOptions().getString("pta");
         pta = World.getResult(ptaId);
         // You can do initialization work here

     }

     private boolean areOverlapped(Var base, Var p){
         Set<Obj> basePtr = pta.getPointsToSet(base);
         Set<Obj> pPtr = pta.getPointsToSet(p);
         for(Obj obj : basePtr){
             if(pPtr.contains(obj)){
                 return true;
             }
         }
         return false;
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
         return out.copyFrom(in);
     }

     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         if(stmt instanceof LoadField) {
             if(((LoadField) stmt).isStatic()){
                 /* e.g.
                     T.f = 100
                     x = T.f
                     int y = 200
                     T.f = y
                 */
                 Var x = ((LoadField) stmt).getLValue();
                 Value xVal = in.get(x);
                 JField staticField = ((LoadField) stmt).getFieldAccess().getFieldRef().resolve();
                 //遍历所有StoreField
                 List<JMethod> rmList = pta.getCallGraph().reachableMethods().collect(Collectors.toList());
                 for(JMethod rm : rmList){
                     for(Stmt stmt1 : rm.getIR().getStmts()){
                         if (stmt1 instanceof StoreField && ((StoreField) stmt1).isStatic()) {
                             JField field = ((StoreField) stmt1).getFieldRef().resolve();
                             if(staticField.equals(field)){
                                 Var var = ((StoreField) stmt1).getRValue();
                                 Value value = solver.getResult().getInFact(stmt1).get(var);
                                 xVal = cp.meetValue(xVal, value);
                             }
                         }
                     }
                 }
                 CPFact result = in.copy();
                 result.remove(x);
                 result.update(x, xVal);
                 return out.copyFrom(result);
             }
             else{
                 /*
                    y = 5
                    pBase.f = y // pBase.f is an alias of xBase.f
                    ...
                    x = xBase.f
                 */
                 Var x = ((LoadField) stmt).getLValue();
                 Value xVal = in.get(x);
                 FieldAccess fieldAccess = ((LoadField) stmt).getFieldAccess();
                 assert fieldAccess instanceof InstanceFieldAccess;
                 JField instanceField = fieldAccess.getFieldRef().resolve();
                 Var xBase = ((InstanceFieldAccess) fieldAccess).getBase();
                 //遍历StoreField
                 List<JMethod> rmList = pta.getCallGraph().reachableMethods().collect(Collectors.toList());
                 for(JMethod rm : rmList){
                     for(Stmt stmt1 : rm.getIR().getStmts()){
                         if (stmt1 instanceof StoreField && !((StoreField) stmt1).isStatic()) {
                             FieldAccess fieldAccess1 = ((StoreField) stmt1).getFieldAccess();
                             assert fieldAccess1 instanceof InstanceFieldAccess;
                             JField instanceField1 = fieldAccess1.getFieldRef().resolve();
                             Var pBase = ((InstanceFieldAccess) fieldAccess1).getBase();
                             if(areOverlapped(xBase, pBase) && instanceField.equals(instanceField1)){
                                 Var var = ((StoreField) stmt1).getRValue();
                                 Value value = solver.getResult().getInFact(stmt1).get(var);
                                 xVal = cp.meetValue(xVal, value);
                             }
                         }
                     }
                 }
                 CPFact result = in.copy();
                 result.remove(x);
                 result.update(x, xVal);
                 return out.copyFrom(result);
             }
         }
         else if(stmt instanceof LoadArray) {
             /*
                int y = 5;
                pArr[j] = y;
                ...
                x = xArr[i];
             */
             Var x = ((LoadArray) stmt).getLValue();
             Value xVal = in.get(x);
             ArrayAccess arrayAccess = ((LoadArray) stmt).getArrayAccess();
             Var xArr = arrayAccess.getBase();
             Var xIndex = arrayAccess.getIndex();
             //遍历所有StoreArray
             List<JMethod> rmList = pta.getCallGraph().reachableMethods().collect(Collectors.toList());
             for(JMethod rm : rmList){
                 for(Stmt stmt1 : rm.getIR().getStmts()){
                     if(stmt1 instanceof StoreArray){
                         ArrayAccess arrayAccess1 = ((StoreArray) stmt1).getArrayAccess();
                         Var pArr = arrayAccess1.getBase();
                         Var pIndex = arrayAccess1.getIndex();
                         if(areOverlapped(xArr, pArr)){
                             Value xIndexVal = in.get(xIndex);
                             Value pIndexVal = solver.getResult().getInFact(stmt1).get(pIndex);
                             if(xIndexVal.isConstant()){
                                if((pIndexVal.isConstant() && xIndexVal.getConstant() == pIndexVal.getConstant()) || pIndexVal.isNAC()){
                                    Var var = ((StoreArray) stmt1).getRValue();
                                    Value value = solver.getResult().getInFact(stmt1).get(var);
                                    xVal = cp.meetValue(xVal, value);
                                }
                             }
                             else if(xIndexVal.isNAC()){
                                if(!pIndexVal.isUndef()){
                                    Var var = ((StoreArray) stmt1).getRValue();
                                    Value value = solver.getResult().getInFact(stmt1).get(var);
                                    xVal = cp.meetValue(xVal, value);
                                }
                             }
                         }
                     }
                 }
             }
             CPFact result = in.copy();
             result.remove(x);
             result.update(x, xVal);
             return out.copyFrom(result);
         }
         else{
             return cp.transferNode(stmt, in, out);
         }
     }

     @Override
     protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
         return out.copy();
     }

     @Override
     protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
         Stmt callSite = edge.getSource();
         assert callSite instanceof Invoke;
         if(((Invoke) callSite).getResult() == null){
             //o.m()
             return out.copy();
         }
         else{
             //a = o.m()
             Var result = ((Invoke) callSite).getResult();
             CPFact ret = out.copy();
             ret.update(result, Value.getUndef());
             return ret;
         }
     }

     @Override
     protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
         CPFact paramIn = new CPFact();
         Stmt callSite = edge.getSource();
         assert callSite instanceof Invoke;
         InvokeExp invokeExp = ((Invoke) callSite).getInvokeExp();
         JMethod callee = edge.getCallee();
         List<Var> params = callee.getIR().getParams();
         for(int i = 0; i < params.size(); ++i){
             Var arg = invokeExp.getArg(i);
             paramIn.update(params.get(i), callSiteOut.get(arg));
         }
         return paramIn;
     }

     @Override
     protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
         CPFact returnSiteIn = new CPFact();
         Stmt callSite = edge.getCallSite();
         assert callSite instanceof Invoke;
         if(((Invoke) callSite).getResult() == null){
             return returnSiteIn;
         }
         else{
             List<Var> returnVars = edge.returnVars().collect(Collectors.toList());
             Value value = returnOut.get(returnVars.get(0));
             for(int i = 1; i < returnVars.size(); ++i){
                 value = cp.meetValue(value, returnOut.get(returnVars.get(i)));
             }
             returnSiteIn.update(((Invoke) callSite).getResult(), value);
             return returnSiteIn;
         }
     }
 }
