package zw494.Optimization;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import zw494.Assembly.BinOp;
import zw494.Assembly.Imm;
import zw494.Assembly.Instr;
import zw494.Assembly.Mem;
import zw494.Assembly.Register;
import zw494.Assembly.Tile;
import zw494.Assembly.UnOp;
import zw494.Assembly.Register.regNames;
import zw494.Assembly.UnOp.UnOpType;
import zw494.CFG.ControlFlowGraphAssembly;

/**
 * The algorithm of the graph coloring register allocation.
 */
public class RegisterAlloc {

    public int memoryNum = 0; // memory offset.

    private Map<String, Register.regNames> curMap; // current coloring

    public RegisterAlloc() {

    }

    // get a new memory offset.
    public int newMemoryOffset() {
        return memoryNum++;
    }

    // get a new piece of memory for the instruction i and its memory offset.
    public Mem getMemory(Instr i, int thisMemNum) {
        Mem m = new Mem(new Register(regNames.rsp), (long) (thisMemNum * 8) + i.stackOffset + 8);

        return m;

    }

    /**
     * Allocate colors for the set instrs.
     * @param instrs the set of instructions to allocate color. Most registers in this set is abstract.
     * @return The result of allocation. All registers are concrete here.
     */
    public List<Instr> allocate(List<Instr> instrs) {

        replaceMemStackOffset(instrs);

        ControlFlowGraphAssembly cfg = new ControlFlowGraphAssembly();

        cfg.createGraph(instrs);

        LiveVarsAnal lva = new LiveVarsAnal(cfg, instrs);

        lva.worklistAlgoBackward();

        Set<Register> checkSet = new HashSet<>();

        IntfGraphTest graph = new IntfGraphTest(lva, instrs);

        graph.build(lva, instrs);

        for (Register r : graph.adjList.keySet()) {
            Set<Register> val = graph.adjList.get(r);

        }

        graph.makeWorkList();

        while (isSimplify(graph)) {
            if (!graph.simplifyWorklist.isEmpty())
                graph.simplify(lva, instrs);
            else if (!graph.worklistMoves.isEmpty())
                graph.coalesce();
            else if (!graph.freezeWorklist.isEmpty()) {
                graph.freeze();
            } else if (!graph.spillWorklist.isEmpty()) {
                graph.selectSpill();
            }
        }

        graph.assignColors();

        if (!graph.spilledNodes.isEmpty()) {
            graph.rewriteProgram(this, lva, instrs);
            return allocate(instrs);
        }

        curMap = graph.colorMap;

        return instrs;
    }

    // boolean isSimplify(IntfGraph g) {
    // return !g.simplifyWorklist.isEmpty() || !g.worklistMoves.isEmpty() ||
    // !g.freezeWorklist.isEmpty()
    // || !g.spillWorklist.isEmpty();
    // }

    // check if the interference graph is simplified.
    boolean isSimplify(IntfGraphTest g) {
        return !g.simplifyWorklist.isEmpty() || !g.worklistMoves.isEmpty() || !g.freezeWorklist.isEmpty()
                || !g.spillWorklist.isEmpty();
    }

    // the current coloring map.
    public Map<String, Register.regNames> curMap() {
        return curMap;
    }

    /**
     * Stores the memory stack offset that should belong to the current instruction.
     */
    public void replaceMemStackOffset(List<Instr> instrs) {

        int stackOffset = 0;

        for (Instr i : instrs) {

            i.stackOffset = stackOffset;

            if (i instanceof UnOp) {
                UnOp j = (UnOp) i;

                if (j.op == UnOpType.pushq) {

                    stackOffset += 8;

                }

            }

            if (i instanceof BinOp) {
                BinOp j = (BinOp) i;

                if (j.arg2 instanceof Register) {
                    Register reg = (Register) j.arg2;
                    if (reg.getRegNames() == regNames.rsp) {
                        if (j.arg1 instanceof Imm) {
                            Imm im = (Imm) j.arg1;
                            stackOffset -= im.value();
                        } else {
                            System.out.println("Not an immediate");
                        }
                    }
                }
            }

        }

    }

}
