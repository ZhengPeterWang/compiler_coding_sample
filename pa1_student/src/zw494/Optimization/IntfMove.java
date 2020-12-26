package zw494.Optimization;

import zw494.Assembly.BinOp;
import zw494.Assembly.Instr;
import zw494.Assembly.Register;

// Defines the move instructions used in the interference graph.
public class IntfMove {
    Instr move; // must be a move related instruction

    enum Category {
        coalesced, constrained, frozen, worklist, active
    }

    // the category of this move.
    Category category;

    public IntfMove(Instr i) {
        if (!(IntfGraph.isMoveInstr(i))) {
            throw new Error("Failed to create move intf node");
        }

        category = Category.worklist;

        move = i;
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof IntfMove))
            return false;
        IntfMove n = (IntfMove) o;
        return n.move.equals(move);
    }

    Register x() {
        BinOp m = (BinOp) move;
        return (Register) m.arg1;

    }

    Register y() {
        BinOp m = (BinOp) move;
        return (Register) m.arg2;

    }

    public int hashCode() {
        return move.hashCode();
    }

}
