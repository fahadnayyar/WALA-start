/*
 * Author: Fahad Nayyar (July, 2021)
 *  TODO: add description of this class
 */

package com.ibm.wala.examples.hotvariablesanalysis;
import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.ssa.*;
import com.ibm.wala.util.collections.Iterator2Iterable;
import com.ibm.wala.util.collections.Pair;
import java.util.*;

public class TotalQueriesAnalysis {

    // * helper methods
    public static void println(Object str) {
        System.out.println(str.toString());
    }
    public static void print(Object str) {
        System.out.print(str.toString());
    }

    public static Pair < Map < ISSABasicBlock, Pair < Integer, Integer > >,
            Map < SSAInstruction, Pair < Integer, Integer> > > perform(IR ir) {
        println("starting!");
        return  perform(ir.getControlFlowGraph(), ir.getSymbolTable());
    }

    public static Pair < Map < ISSABasicBlock, Pair < Integer, Integer > >,
            Map < SSAInstruction, Pair < Integer, Integer> > > perform(
            final ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg, final SymbolTable symtab) {

        //* Array of all instructions in the cgf
        final SSAInstruction[] instructions = cfg.getInstructions();

        //* Initializing the flow sets.
        Map < ISSABasicBlock, Pair < Integer, Integer> > flowSetsBB = new HashMap < ISSABasicBlock, Pair <Integer, Integer> >();
        Map < SSAInstruction, Pair < Integer, Integer> > flowSetsInstr = new HashMap < SSAInstruction, Pair <Integer, Integer> >();

        //* Initializing the visited map for bfs
        Map<ISSABasicBlock, Integer> visitedMap = new HashMap<ISSABasicBlock, Integer>();

        //* Iterating over all exit basic blocks of cfg to mark 0 in visited map, initialize flowSetsBB and flowSetsInst.
//        println("Iterating over all exit basic blocks of cfg to mark 0 in visited map, initialize flowSetsBB and flowSetsInst");
        Iterator<ISSABasicBlock> bbIterator = cfg.stream().iterator();
        while (bbIterator.hasNext()) {
            ISSABasicBlock currentBB = (ISSABasicBlock) bbIterator.next();
            print("Iterating over Basic Block: "); println(bbIterator);
            //* Mark not visited for currBB(0)
            visitedMap.put(currentBB, new Integer(0));
            //* Initialize entry and exit flow set of currBB to 0
            Pair<Integer, Integer> currBBFlowSets = Pair.make(new Integer(0), new Integer(0));
            flowSetsBB.put(currentBB, currBBFlowSets);
            for (int i = currentBB.getLastInstructionIndex(); i >= currentBB.getFirstInstructionIndex(); i--) {
                SSAInstruction currInstr = instructions[i];
                //* Initialize entry and exit flow set of currInstr to 0
                Pair<Integer, Integer> currInstrFlowSets = Pair.make(new Integer(0), new Integer(0));
                flowSetsInstr.put(currInstr, currInstrFlowSets);
            }
        }

        //* Level order traversal (bfs)
//        println("Level order traversal (bfs):");
        //* Initializing bfs queue
        Queue<ISSABasicBlock> bfsQueue = new LinkedList<ISSABasicBlock>();
        ISSABasicBlock exitBB = cfg.exit();
        print("Exit basic block: "); println(exitBB);
        //* Inserting exit basic block in bfs queue
//        println("Inserting exit basic block in bfs queue");
        bfsQueue.add(exitBB);
        while(!bfsQueue.isEmpty()) {
            ISSABasicBlock currentBB = (ISSABasicBlock) bfsQueue.remove();
            //* Process the currentBB only if it was not visited earlier
            if (visitedMap.get(currentBB) == 0) {
                print("Visited BB: ");
                println(currentBB.toString());
                //* Mark currentBB as visited as it will be processed now
                visitedMap.put(currentBB, new Integer(1));
                //* Properly initializing the inValBB and outValBB
                int inValBB = 0;
                int outValBB = 0;
                for (ISSABasicBlock succBB : Iterator2Iterable.make(cfg.getSuccNodes(currentBB))){
                    int succInVal = flowSetsBB.get(succBB).fst;
                    outValBB += succInVal;
                }
                inValBB = outValBB;
                //* Iterating over the Instructions of this BB in reverse to update the flowsets:
                for (int i = currentBB.getLastInstructionIndex(); i >= currentBB.getFirstInstructionIndex(); i--) {
                    SSAInstruction currInstr = instructions[i];
                    int outVal = 0;
                    if (i!=currentBB.getLastInstructionIndex()) {
                        outVal = flowSetsInstr.get(instructions[i+1]).fst;

                    }else {
                        for (ISSABasicBlock succBB : Iterator2Iterable.make(cfg.getSuccNodes(currentBB))){
                            int succInVal = flowSetsBB.get(succBB).fst;
                            outVal += succInVal;
                        }
                        outValBB = outVal;
                    }
                    int inVal = outVal;
                    if (currInstr instanceof SSAConditionalBranchInstruction){
                        inVal += 1;
                    }
                    inValBB = inVal;
                    Pair<Integer, Integer> currInstrFlowSets = Pair.make(new Integer(inVal), new Integer(outVal));
                    flowSetsInstr.put(currInstr, currInstrFlowSets);
                }
                Pair<Integer, Integer> currBBFlowSets = Pair.make(new Integer(inValBB), new Integer(outValBB));
                flowSetsBB.put(currentBB, currBBFlowSets);
                //* Pushing predecessors of currentBB into the bfs queue
//                println("Pushing predecessors of currentBB into the bfs queue");
                for (ISSABasicBlock predBB : Iterator2Iterable.make(cfg.getPredNodes(currentBB))) {
                    if (visitedMap.get(predBB) == 0) {
                        bfsQueue.add(predBB);
                    }
                }
            }
        }

        //* DEBUGGING: Priting entry basic block
        ISSABasicBlock entryBB = (ISSABasicBlock) cfg.entry();
        print("Entry basic block: "); println(entryBB);

        Pair < Map < ISSABasicBlock, Pair < Integer, Integer > >,
                Map < SSAInstruction, Pair < Integer, Integer> > > returnPair = Pair.make(flowSetsBB, flowSetsInstr);

        return returnPair;
//        return perform(cfg, symtab, new BitVector());
    }
}