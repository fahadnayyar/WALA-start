package com.ibm.wala.examples.hotvariablesanalysis;

/*******************************************************************************
 * Copyright (c) 2008 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *******************************************************************************/

import java.io.IOException;

import com.ibm.wala.classLoader.IClass;
import com.ibm.wala.classLoader.IMethod;
import com.ibm.wala.examples.drivers.ConstructAllIRs; // TODO: make a new file in this package
import com.ibm.wala.ipa.callgraph.AnalysisCacheImpl;
import com.ibm.wala.ipa.callgraph.AnalysisOptions;
import com.ibm.wala.ipa.callgraph.AnalysisScope;
import com.ibm.wala.ipa.callgraph.IAnalysisCacheView;
import com.ibm.wala.ipa.callgraph.impl.Everywhere;
import com.ibm.wala.ipa.cha.ClassHierarchy;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.ipa.cha.ClassHierarchyFactory;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.perf.Stopwatch;
//import com.ibm.wala.util.ref.ReferenceCleanser;
import com.ibm.wala.examples.hotvariablesanalysis.TotalQueriesAnalysis;
import com.ibm.wala.ssa.IR;

/**
 * An analysis skeleton that simply constructs IRs for all methods in a class hierarchy. Illustrates the use of
 * {@link TotalQueriesAnalysis} to TODO: fill.
 */
public class TotalQueriesAnalysisDriver {

    /**
     * First command-line argument should be location of scope file for application to analyze
     *
     * @throws IOException
     * @throws ClassHierarchyException
     */
    public static void main(String[] args) throws IOException, ClassHierarchyException {
        String scopeFile = args[0];

        // measure running time
        Stopwatch s = new Stopwatch();
        s.start();
        AnalysisScope scope = AnalysisScopeReader.readJavaScope(scopeFile, null, ConstructAllIRs.class.getClassLoader());

        // build a type hierarchy
        System.out.print("building class hierarchy...");
        ClassHierarchy cha = ClassHierarchyFactory.make(scope);
        System.out.println("done");

        // register class hierarchy and AnalysisCache with the reference cleanser, so that their soft references are appropriately wiped
//        ReferenceCleanser.registerClassHierarchy(cha);
        AnalysisOptions options = new AnalysisOptions();
        IAnalysisCacheView cache = new AnalysisCacheImpl(options.getSSAOptions());
//        ReferenceCleanser.registerCache(cache);

        System.out.println("building IRs...");
        for (IClass klass : cha) {
            if (klass.getName().toString().compareTo("Lcom/ibm/wala/examples/testcases/Test1")==0) {
                // could also be written: if (klass.getSourceFileName().compareTo("Test1.java") == 0 )
                System.out.println("yeah1!");
                System.out.println(klass.getSourceFileName());
                System.out.println(klass.getName().toString());
            }else {
//                System.out.println(klass.getSourceFileName());
//                System.out.println(klass.getName().toString());
                continue;
            }
            for (IMethod method : klass.getDeclaredMethods()) {
                if (method.getName().toString().compareTo("main")==0) {
                    System.out.println("yeah2!!");
                    System.out.println(method.getName().toString());



                    // Here: write code to be analyzed on main method in Test1.java file (Test1 class)
                    // construct an IR
                    IR ir = cache.getIR(method, Everywhere.EVERYWHERE);
                    TotalQueriesAnalysis totalQueriesAnalysis = new TotalQueriesAnalysis();
                    if (ir != null) {
                        System.out.println(ir.toString());
                        System.out.println(totalQueriesAnalysis.perform(ir));
                    }


                }
//                System.out.println(method.getName().toString());

            }
        }
        System.out.println("done");
        s.stop();
        System.out.println("RUNNING TIME: " + s.getElapsedMillis());
    }
}
