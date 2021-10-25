package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import polyglot.ast.Call;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.getClassHierarchy();
        return buildCallGraph(World.getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while(!workList.isEmpty()){
            JMethod jMethod = workList.poll();
            if(!callGraph.contains(jMethod)){
                callGraph.addReachableMethod(jMethod);
                callGraph.callSitesIn(jMethod).forEach(invoke -> {
                    Set<JMethod> targets = resolve(invoke);
                    for(JMethod target : targets){
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),invoke,target));
                        workList.add(target);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> targets = new HashSet<>();
        if(CallGraphs.getCallKind(callSite) == CallKind.STATIC){
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JMethod target = declaringClass.getDeclaredMethod(subsignature);
            assert target != null;
            targets.add(target);
        }
        else if(CallGraphs.getCallKind(callSite) == CallKind.SPECIAL){
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            JMethod target = dispatch(declaringClass, subsignature);
            assert target != null;
            targets.add(target);
        }
        else if(CallGraphs.getCallKind(callSite) == CallKind.VIRTUAL || CallGraphs.getCallKind(callSite) == CallKind.INTERFACE){
            JClass declaringClass = callSite.getMethodRef().getDeclaringClass();
            Subsignature subsignature = callSite.getMethodRef().getSubsignature();
            if(declaringClass.isInterface()){
                for(JClass jClass : new ArrayList<>(hierarchy.getDirectSubinterfacesOf(declaringClass))){
                    JMethod target = dispatch(jClass, subsignature);
                    if(target != null && !target.isAbstract()){
                        targets.add(target);
                    }
                }
                for(JClass jClass : new ArrayList<>(hierarchy.getDirectImplementorsOf(declaringClass))){
                    JMethod target = dispatch(jClass, subsignature);
                    if(target != null && !target.isAbstract()){
                        targets.add(target);
                    }
                }
            }
            else{
                JMethod target = dispatch(declaringClass, subsignature);
                if(target != null && !target.isAbstract()){
                    targets.add(target);
                }
                for(JClass jClass : new ArrayList<>(hierarchy.getDirectSubclassesOf(declaringClass))){
                    target = dispatch(jClass, subsignature);
                    if(target != null && !target.isAbstract()){
                        targets.add(target);
                    }
                }
            }
        }
        else{
        }
        return targets;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if(jclass == null)
            return null;
        if(jclass.isInterface()){
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        else{
            JMethod jMethod = jclass.getDeclaredMethod(subsignature);
            if(jMethod == null){
                return dispatch(jclass.getSuperClass(), subsignature);
            }
            else{
                return jMethod;
            }
        }
    }
}
