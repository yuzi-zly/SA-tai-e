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

 import jas.CP;
 import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
 import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
 import pascal.taie.analysis.dataflow.analysis.constprop.Value;
 import pascal.taie.analysis.graph.cfg.CFG;
 import pascal.taie.analysis.graph.cfg.CFGBuilder;
 import pascal.taie.analysis.graph.icfg.CallEdge;
 import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
 import pascal.taie.analysis.graph.icfg.NormalEdge;
 import pascal.taie.analysis.graph.icfg.ReturnEdge;
 import pascal.taie.config.AnalysisConfig;
 import pascal.taie.ir.IR;
 import pascal.taie.ir.exp.InvokeExp;
 import pascal.taie.ir.exp.Var;
 import pascal.taie.ir.stmt.Invoke;
 import pascal.taie.ir.stmt.Stmt;
 import pascal.taie.language.classes.JMethod;

 import java.util.List;
 import java.util.stream.Collectors;

 /**
  * Implementation of interprocedural constant propagation for int values.
  */
 public class InterConstantPropagation extends
         AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

     public static final String ID = "inter-constprop";

     private final ConstantPropagation cp;

     public InterConstantPropagation(AnalysisConfig config) {
         super(config);
         cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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
         // x = o.m() or o.m()
         return out.copyFrom(in);
     }

     @Override
     protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
         return cp.transferNode(stmt, in, out);
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
