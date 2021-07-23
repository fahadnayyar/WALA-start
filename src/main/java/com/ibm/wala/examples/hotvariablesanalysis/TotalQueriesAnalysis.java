package com.ibm.wala.examples.hotvariablesanalysis;

/*
 * Copyright (c) 2002 - 2006 IBM Corporation.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 */

import com.ibm.wala.cfg.ControlFlowGraph;
import com.ibm.wala.dataflow.graph.AbstractMeetOperator;
import com.ibm.wala.dataflow.graph.BitVectorSolver;
import com.ibm.wala.dataflow.graph.BitVectorUnion;
import com.ibm.wala.dataflow.graph.IKilldallFramework;
import com.ibm.wala.dataflow.graph.ITransferFunctionProvider;
import com.ibm.wala.fixpoint.BitVectorVariable;
import com.ibm.wala.fixpoint.UnaryOperator;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.ISSABasicBlock;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPhiInstruction;
import com.ibm.wala.ssa.SymbolTable;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.CancelRuntimeException;
import com.ibm.wala.util.collections.Iterator2Iterable;
import com.ibm.wala.util.collections.Pair;
import com.ibm.wala.util.debug.Assertions;
import com.ibm.wala.util.graph.Graph;
import com.ibm.wala.util.graph.impl.GraphInverter;
import com.ibm.wala.util.intset.BitVector;
import com.ibm.wala.util.intset.BitVectorIntSet;
import com.ibm.wala.util.intset.IntSet;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Julian Dolby
 *     <p>Live-value analysis for a method's IR (or {@link ControlFlowGraph} and {@link
 *     SymbolTable}) using a {@link IKilldallFramework} based implementation.
 *     <p>Pre-requisites - Knowledge of SSA form: control flow graphs, basic blocks, Phi
 *     instructions - Knowledge of data flow analysis theory: see
 *     http://en.wikipedia.org/wiki/Data_flow_analysis
 *     <p>Implementation notes:
 *     <p>- The solver uses node transfer functions only. - Performance: inverts the CFG to traverse
 *     backwards (backward analysis).
 */
public class TotalQueriesAnalysis {

    public interface Result {
        boolean isLiveEntry(ISSABasicBlock bb, int valueNumber);

        boolean isLiveExit(ISSABasicBlock bb, int valueNumber);

        BitVector getLiveBefore(int instr);
    }

    /** */
    public static Result perform(IR ir) {
        return perform(ir.getControlFlowGraph(), ir.getSymbolTable());
    }

    /** */
    public static Result perform(
            final ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg, final SymbolTable symtab) {
        return perform(cfg, symtab, new BitVector());
    }

    /**
     * @param considerLiveAtExit given set (of variables) to consider to be live after the exit.
     *     <p>todo: used once in {@link com.ibm.wala.cast.ir.ssa.SSAConversion}; Explain better the
     *     purpose.
     */
    public static Result perform(
            final ControlFlowGraph<SSAInstruction, ISSABasicBlock> cfg,
            final SymbolTable symtab,
            final BitVector considerLiveAtExit) {
        final BitVectorIntSet liveAtExit = new BitVectorIntSet(considerLiveAtExit);
        final SSAInstruction[] instructions = cfg.getInstructions();

        Map < SSAInstruction, Pair < BitVectorVariable, BitVectorVariable > > flowSetsMap = new HashMap();

        /* Gen/kill operator specific to exit basic blocks */
        final class ExitBlockGenKillOperator extends UnaryOperator<BitVectorVariable> {
            @Override
            public String toString() {
                return "ExitGenKill";
            }

            @Override
            public boolean equals(Object o) {
                return o == this;
            }

            @Override
            public int hashCode() {
                return 37721;
            }

            /** Evaluate the transfer between two nodes in the flow graph within an exit block. */
            @Override
            public byte evaluate(BitVectorVariable lhs, BitVectorVariable rhs) {
                boolean changed =
                        lhs.getValue() == null
                                ? !considerLiveAtExit.isZero()
                                : !lhs.getValue().sameValue(liveAtExit);

                lhs.addAll(considerLiveAtExit);

                return changed ? CHANGED : NOT_CHANGED;
            }
        }

        /* Gen/kill operator for a regular basic block. */
        final class BlockValueGenKillOperator extends UnaryOperator<BitVectorVariable> {
            private final ISSABasicBlock block;

            BlockValueGenKillOperator(ISSABasicBlock block) {
                this.block = block;
            }

            @Override
            public String toString() {
                return "GenKill:" + block;
            }

            @Override
            public boolean equals(Object o) {
                return (o instanceof BlockValueGenKillOperator)
                        && ((BlockValueGenKillOperator) o).block.equals(block);
            }

            @Override
            public int hashCode() {
                return block.hashCode() * 17;
            }

            /** Kills the definitions (variables written to). */
            private void processDefs(SSAInstruction inst, BitVector bits) {
                for (int j = 0; j < inst.getNumberOfDefs(); j++) {
                    bits.clear(inst.getDef(j));
                }
            }

            /** Generates variables that are read (skips constants). */
            private void processUses(SSAInstruction inst, BitVector bits) {
                for (int j = 0; j < inst.getNumberOfUses(); j++) {
                    assert inst.getUse(j) != -1 : inst.toString();
                    if (!symtab.isConstant(inst.getUse(j))) {
                        bits.set(inst.getUse(j));
                    }
                }
            }

            /** Evaluate the transfer between two nodes in the flow graph within one basic block. */
            @Override
            public byte evaluate(BitVectorVariable lhs, BitVectorVariable rhs) {
                // Calculate here the result of the transfer
                BitVectorIntSet bits = new BitVectorIntSet();

                IntSet s = rhs.getValue();
                if (s != null) {
                    bits.addAll(s);
                }
                // Include all uses generated by the current basic block into the successor's Phi
                // instructions todo: rephrase
                for (ISSABasicBlock succBB : Iterator2Iterable.make(cfg.getSuccNodes(block))) {

                    int rval = com.ibm.wala.cast.ir.cfg.Util.whichPred(cfg, succBB, block);
                    for (SSAPhiInstruction sphi : Iterator2Iterable.make(succBB.iteratePhis())) {
                        bits.add(sphi.getUse(rval));
                    }
                }
                // For all instructions, in reverse order, 'kill' variables written to and 'gen' variables
                // read.
                for (int i = block.getLastInstructionIndex(); i >= block.getFirstInstructionIndex(); i--) {
                    SSAInstruction inst = instructions[i];
                    if (inst != null) {
                        BitVectorVariable outSet = new BitVectorVariable();
                        BitVectorVariable inSet = new BitVectorVariable();
                        outSet.addAll(bits.getBitVector());

                        processDefs(inst, bits.getBitVector());
                        processUses(inst, bits.getBitVector());

                        inSet.addAll(bits.getBitVector());
                        Pair < BitVectorVariable, BitVectorVariable > flowSet = Pair.make(inSet, outSet);
//                      System.out.println(flowSet.fst.toString() + ", " + flowSet.snd.toString());
                        flowSetsMap.put(inst, flowSet);
                    }
                }

                // 'kill' the variables defined by the Phi instructions in the current block.
                for (SSAInstruction S : Iterator2Iterable.make(block.iteratePhis())) {
                    BitVectorVariable outSet = new BitVectorVariable();
                    BitVectorVariable inSet = new BitVectorVariable();
                    outSet.addAll(bits.getBitVector());

                    processDefs(S, bits.getBitVector());

                    inSet.addAll(bits.getBitVector());
                    Pair < BitVectorVariable, BitVectorVariable > flowSet = Pair.make(inSet, outSet);
//                    System.out.println(flowSet.fst.toString() + ", " + flowSet.snd.toString());
                    flowSetsMap.put(S, flowSet);
                }

                BitVectorVariable U = new BitVectorVariable();
                U.addAll(bits.getBitVector());

                if (!lhs.sameValue(U)) {
                    lhs.copyState(U);
                    return CHANGED;
                } else {
                    return NOT_CHANGED;
                }
            }
        }

        /* Create the solver */
        final BitVectorSolver<ISSABasicBlock> S =
                new BitVectorSolver<>(
                        new IKilldallFramework<ISSABasicBlock, BitVectorVariable>() {
                            private final Graph<ISSABasicBlock> G = GraphInverter.invert(cfg);

                            @Override
                            public Graph<ISSABasicBlock> getFlowGraph() {
                                return G;
                            }

                            @Override
                            public ITransferFunctionProvider<ISSABasicBlock, BitVectorVariable>
                            getTransferFunctionProvider() {
                                return new ITransferFunctionProvider<ISSABasicBlock, BitVectorVariable>() {

                                    @Override
                                    public boolean hasNodeTransferFunctions() {
                                        return true;
                                    }

                                    @Override
                                    public boolean hasEdgeTransferFunctions() {
                                        return false;
                                    }

                                    /** Create the specialized operator for regular and exit basic blocks. */
                                    @Override
                                    public UnaryOperator<BitVectorVariable> getNodeTransferFunction(
                                            ISSABasicBlock node) {
                                        if (node.isExitBlock()) {
                                            System.out.println("HAHAH!");
                                            System.out.println(node);
                                            return new ExitBlockGenKillOperator();
                                        } else {
                                            return new BlockValueGenKillOperator(node);
                                        }
                                    }

                                    @Override
                                    public UnaryOperator<BitVectorVariable> getEdgeTransferFunction(
                                            ISSABasicBlock s, ISSABasicBlock d) {
                                        Assertions.UNREACHABLE();
                                        return null;
                                    }

                                    /** Live analysis uses 'union' as 'meet operator' */
                                    @Override
                                    public AbstractMeetOperator<BitVectorVariable> getMeetOperator() {
                                        return BitVectorUnion.instance();
                                    }
                                };
                            }
                        });

        /* Solve the analysis problem */
        try {
            S.solve(null);
        } catch (CancelException e) {
            throw new CancelRuntimeException(e);
        }

        /* Prepare the lazy result with a closure. */
        return new Result() {

            @Override
            public String toString() {
                StringBuilder s = new StringBuilder();
                for (int i = 0; i < cfg.getNumberOfNodes(); i++) {
                    ISSABasicBlock bb = cfg.getNode(i);
                    s.append("live entering ").append(bb).append(':').append(S.getOut(bb)).append('\n');
                    s.append("live exiting ").append(bb).append(':').append(S.getIn(bb)).append('\n');
                }
                s.append("\n\nINSTRUCTIONS FLOW-SETS: \n\n");
                for (Map.Entry< SSAInstruction, Pair < BitVectorVariable, BitVectorVariable > > entry : flowSetsMap.entrySet()){
//                  System.out.println("Key = " + entry.getKey() + ", Value = " + entry.getValue());
                    Pair<BitVectorVariable, BitVectorVariable> flowSets = (Pair<BitVectorVariable, BitVectorVariable>)entry.getValue();
                    if (flowSets == null) {
                        continue;
                    }
                    BitVectorVariable inSet = (BitVectorVariable) flowSets.fst;
                    BitVectorVariable outSet = (BitVectorVariable) flowSets.snd;
                    String inSetStr = inSet.toString();
                    String outSetStr = outSet.toString();
                    String instrStr = entry.getKey().toString();
                    s.append("inSet of "); s.append(instrStr); s.append(" : "); s.append(inSetStr); s.append("\n");
                    s.append("outSet of "); s.append(instrStr); s.append(" : "); s.append(outSetStr); s.append("\n");
                }
                return s.toString();
            }

            @Override
            public boolean isLiveEntry(ISSABasicBlock bb, int valueNumber) {
                return S.getOut(bb).get(valueNumber);
            }

            @Override
            public boolean isLiveExit(ISSABasicBlock bb, int valueNumber) {
                return S.getIn(bb).get(valueNumber);
            }

            /**
             * Calculate set of variables live before instruction {@code instr}.
             *
             * @see <a href="http://en.wikipedia.org/wiki/Data_flow_analysis#Backward_Analysis">how the
             *     "in" and "out" variable sets work</a>
             */
            @Override
            public BitVector getLiveBefore(int instr) {
                ISSABasicBlock bb = cfg.getBlockForInstruction(instr);

                // Start with the variables live at the 'in' of the basic block of the instruction. todo???
                BitVectorIntSet bits = new BitVectorIntSet();
                IntSet s = S.getIn(bb).getValue();
                if (s != null) {
                    bits.addAll(s);
                }
                // For all instructions in the basic block, going backwards, from the last,
                // up to the desired instruction, 'kill' written variables and 'gen' read variables.
                for (int i = bb.getLastInstructionIndex(); i >= instr; i--) {
                    SSAInstruction inst = instructions[i];
                    if (inst != null) {
                        for (int j = 0; j < inst.getNumberOfDefs(); j++) {
                            bits.remove(inst.getDef(j));
                        }
                        for (int j = 0; j < inst.getNumberOfUses(); j++) {
                            if (!symtab.isConstant(inst.getUse(j))) {
                                bits.add(inst.getUse(j));
                            }
                        }
                    }
                }

                return bits.getBitVector();
            }
        };
    }
}