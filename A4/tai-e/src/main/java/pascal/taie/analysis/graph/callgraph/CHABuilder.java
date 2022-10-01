/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod caller = workList.peek();
            workList.remove();
            if (callGraph.addReachableMethod(caller)) {
                List<Invoke> callSites = callGraph.callSitesIn(caller).toList();
                for (Invoke callSite : callSites) {
                    Set<JMethod> callees = resolve(callSite);
                    for (JMethod callee : callees) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, callee));
                    }

                    workList.addAll(callees);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> methods = new HashSet<>();
        CallKind callKind = CallGraphs.getCallKind(callSite);
        switch (callKind) {
            case STATIC -> {
                JClass jclass = callSite.getMethodRef().getDeclaringClass();
                Subsignature subsignature = callSite.getMethodRef().getSubsignature();
                methods.add(jclass.getDeclaredMethod(subsignature));
            }
            case SPECIAL -> {
                JClass jclass = callSite.getMethodRef().getDeclaringClass();
                Subsignature subsignature = callSite.getMethodRef().getSubsignature();
                methods.add(dispatch(jclass, subsignature));
            }
            default -> {
                JClass jclass = callSite.getMethodRef().getDeclaringClass();
                Subsignature subsignature = callSite.getMethodRef().getSubsignature();

                // use workList to traversal all subclass
                Queue<JClass> workList  = new LinkedList<>();
                workList.add(jclass);
                while (!workList.isEmpty()) {
                    jclass = workList.peek();
                    workList.remove();
                    JMethod method = dispatch(jclass, subsignature);
                    if (method != null) methods.add(method);

                    if (jclass.isInterface()) {
                        workList.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                        workList.addAll(hierarchy.getDirectImplementorsOf(jclass));
                    } else {
                        workList.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                }
            }
        }

        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod declaredMethod = jclass.getDeclaredMethod(subsignature);
        JClass superClass = jclass.getSuperClass();

        if (declaredMethod != null && declaredMethod.isAbstract()) {
            declaredMethod = null;
        }
        if (declaredMethod == null && superClass != null) {
            declaredMethod = dispatch(superClass, subsignature);
        }
        return declaredMethod;
    }
}
