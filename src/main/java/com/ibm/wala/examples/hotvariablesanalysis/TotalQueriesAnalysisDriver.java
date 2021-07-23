/*
 * Author: Fahad Nayyar (July, 2021)
 *  TODO: add description of this class
 */

package com.ibm.wala.examples.hotvariablesanalysis;

import java.io.IOException;
import java.util.HashMap;
import java.util.Map;

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
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.config.AnalysisScopeReader;
import com.ibm.wala.util.perf.Stopwatch;
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
        //* TODO: add usage descripton.

        String scopeFile = args[0];
        String testCLassName = args[1];

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

        System.out.println("building IRs...");
        for (IClass klass : cha) {
            String testCasePath = "Lcom/ibm/wala/examples/testcases/" + testCLassName;
            if (klass.getName().toString().compareTo(testCasePath)==0) {
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
//                        System.out.println(totalQueriesAnalysis.perform(ir));
                        Pair <Map<ISSABasicBlock, Pair< Integer, Integer >>,
                                Map <SSAInstruction, Pair < Integer, Integer> > > returnPair = totalQueriesAnalysis.perform(ir);

                        Map < ISSABasicBlock, Pair < Integer, Integer> > flowSetsBB = returnPair.fst;
                        Map < SSAInstruction, Pair < Integer, Integer> > flowSetsInstr = returnPair.snd;


                        //* OUTPUT-DISPLAY: Printing final flow sets of instructions
                        println("Printing final flow sets of instructions: ");
                        for (Map.Entry < SSAInstruction, Pair < Integer, Integer> > mapElem : flowSetsInstr.entrySet()){
                            Pair<Integer, Integer> currInstrFlowSets = (Pair<Integer, Integer>)mapElem.getValue();
                            SSAInstruction currentInstr = mapElem.getKey();
                            if (currentInstr!=null) {
                                print("INSET: { "); print(currInstrFlowSets.fst); println(" }");
                                print("INSTRUCTION: "); println(currentInstr.toString());
                                print("OUTSET: { "); print(currInstrFlowSets.fst); println(" }");
                            }
                        }

                        //* OUTPUT-DISPLAY: Printing final flow sets of Basic Blocks
                        println("Printing final flow sets of Basic Blocks: ");
                        for (Map.Entry < ISSABasicBlock, Pair < Integer, Integer> > mapElem : flowSetsBB.entrySet()){
                            Pair<Integer, Integer> currInstrFlowSets = (Pair<Integer, Integer>)mapElem.getValue();
                            ISSABasicBlock currentBB = mapElem.getKey();
                            if (currentBB!=null) {
                                print("INSET: { "); print(currInstrFlowSets.fst); println(" }");
                                print("BASIC-BLOCK: "); println(currentBB.toString());
                                print("OUTSET: { "); print(currInstrFlowSets.fst); println(" }");
                            }
                        }
                    }
                }
            }
        }
        System.out.println("done");
        s.stop();
        System.out.println("RUNNING TIME: " + s.getElapsedMillis());
    }

    // * helper methods
    public static void println(Object str) {
        System.out.println(str.toString());
    }
    public static void print(Object str) {
        System.out.print(str.toString());
    }

}
