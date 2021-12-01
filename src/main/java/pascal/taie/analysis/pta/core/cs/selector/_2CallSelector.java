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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        int len = callSite.getContext().getLength();
        if(len == 0){
            return ListContext.make(callSite.getCallSite());
        }
        else{
            return ListContext.make(callSite.getContext().getElementAt(len - 1), callSite.getCallSite());
        }
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        int len = callSite.getContext().getLength();
        if(len == 0){
            return ListContext.make(callSite.getCallSite());
        }
        else{
            return ListContext.make(callSite.getContext().getElementAt(len - 1), callSite.getCallSite());
        }
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        int len = method.getContext().getLength();
        if(len == 0){
            return ListContext.make();
        }
        else{
            return ListContext.make(method.getContext().getElementAt(len - 1));
        }
    }
}
