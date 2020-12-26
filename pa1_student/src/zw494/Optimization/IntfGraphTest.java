package zw494.Optimization;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import zw494.AST.Factory;
import zw494.Assembly.BinOp;
import zw494.Assembly.Instr;
import zw494.Assembly.Mem;
import zw494.Assembly.Register;
import zw494.Assembly.BinOp.OpType;
import zw494.Assembly.Register.Type;
import zw494.Assembly.Register.regNames;
import zw494.Optimization.IntfMove.Category;

/**
 * The interference graph for assembly instructions.
 */ 
public class IntfGraphTest {

    // graph data structure: stored as an adjacent list
    Map<Register, Set<Register>> adjList;
    HashSet<Pair<Register>> adjSet;
    public static Map<String, Map<String, Register.regNames>> globalMapMap;
    public static Map<String, Register.regNames> curGlobalMap;

    // set the current mapping from register names to their color
    public static void setCurGlobalMap(String funcName) {
        curGlobalMap = globalMapMap.get(funcName);
    }

    // the result of the graph coloring algorithm: color allocation!
    Map<String, Register.regNames> colorMap;

    // worklists of nodes
    Set<Register> precolored;
    Set<Register> initial;
    Map<Register, Register> registerSet;
    Queue<Register> simplifyWorklist;
    Queue<Register> freezeWorklist;
    PriorityQueue<Register> spillWorklist;
    Set<Register> spilledNodes;
    Set<Register> coalescedNodes;
    Set<Register> coloredNodes;
    Stack<Register> selectStack;

    // lists of moves
    Set<IntfMove> coalescedMoves;
    Set<IntfMove> constrainedMoves;
    Set<IntfMove> frozenMoves;
    Set<IntfMove> worklistMoves;
    Set<IntfMove> activeMoves;

    // a map from each node to a list of moves that it is associated with
    Map<Register, Set<IntfMove>> moveList;

    // K colour value
    final int K = 14;

    /**
     * Construct the interference graph.
     * 
     * @param lva    Result of the live variable analysis
     * @param instrs the list of instructions that we are processing
     */
    public IntfGraphTest(LiveVarsAnal lva, List<Instr> instrs) {

        adjList = new HashMap<>();
        adjSet = new HashSet<>();

        colorMap = new HashMap<>();

        registerSet = new HashMap<>();
        precolored = new HashSet<>();
        initial = new HashSet<>();
        simplifyWorklist = new LinkedList<>();
        freezeWorklist = new LinkedList<>();
        spillWorklist = new PriorityQueue<>();

        spilledNodes = new HashSet<>();
        coalescedNodes = new HashSet<>();
        coloredNodes = new HashSet<>();

        selectStack = new Stack<>();

        coalescedMoves = new HashSet<>();
        constrainedMoves = new HashSet<>();
        frozenMoves = new HashSet<>();
        worklistMoves = new HashSet<>();
        activeMoves = new HashSet<>();

        moveList = new HashMap<>();

        Set<Register> s = new HashSet<>();

        for (Instr i : instrs) {

            s.addAll(lva.def(i));
            // addAllSet(s, lva.def(i), "instr (lva def)");
            if (lva.use(i) != null)
                s.addAll(lva.use(i));
            // addAllSet(s, lva.use(i), "instr (lva use)");

        }
        for (Register j : s) {
            addNode(j);
        }

    }

    /**
     * Build the interferenece graph
     * 
     * @param lva    Result of the live variable analysis
     * @param instrs the list of instructions that we are processing
     */
    void build(LiveVarsAnal lva, List<Instr> instrs) {

        for (Instr i : instrs) {

            Set<Register> live = new HashSet<>();
            for (Register w : lva.out.get(i)) {
                live.add(registerSet.get(w));
            }
            // live.addAll(lva.out.get(i));
            // addAllSet(live, lva.out.get(i), "live (lva out)");

            if (isMoveInstr(i)) {
                for (Register w : lva.use(i)) {
                    live.remove(registerSet.get(w));
                }
                // live.removeAll(lva.use(i));
                IntfMove move = new IntfMove(i);

                for (Register r : lva.def(i)) {

                    moveListPut(registerSet.get(r), move);
                }
                for (Register r : lva.use(i)) {

                    moveListPut(registerSet.get(r), move);
                }

                move.category = Category.worklist;
                // worklistMoves.add(move);
                addSetMove(worklistMoves, move, "build");

            }
            if (lva.def(i) != null) {
                for (Register w : lva.def(i)) {
                    live.add(registerSet.get(w));
                }
                // live.addAll(lva.def(i));
                // addAllSet(live, lva.def(i), "live (lva def)");
            }

            Set<Register> temp = new HashSet<>();
            for (Register r : lva.def(i)) {
                temp.add(registerSet.get(r));
            }
            // add an edge to all registers that are interfering with each other
            for (Register r : temp) {

                for (Register s : live) {

                    addEdge(r, s);

                }

            }

        }
    }

    /**
     * Create all the worklists.
     */
    void makeWorkList() {
        for (Iterator<Register> iterator = initial.iterator(); iterator.hasNext();) {
            Register n = iterator.next();

            if (getDegree(n) >= K) {

                n.type = Type.spilling;
                // spillWorklist.add(n);
                addQueue(spillWorklist, n, "spill (initial)");

            } else if (moveRelated(n)) {

                n.type = Type.freeze;
                // freezeWorklist.add(n);
                addList(freezeWorklist, n, "freeze (initial)");
                // System.out.println("FREEZING 1:" + n.hashCode() + " " + n);

            } else {

                n.type = Type.simplify;
                // simplifyWorklist.add(n);
                addList(simplifyWorklist, n, "simplify (initial)");

            }

            iterator.remove();
        }

    }

    /**
     * Check if n is move related
     * 
     * @param n The register to check
     * @return whether it is related to a move instruction or not.
     */
    boolean moveRelated(Register n) {

        return !nodeMoves(n).isEmpty();

    }

    /**
     * Get the degree of the the node n.
     * 
     * @param n The register to get the degree
     * @return The degree of the register, which is how many registers are adjacent to n in the interference graph
     */
    int getDegree(Register n) {

        return n.degree;

    }

    /**
     * Do the simplify() algorithm!
     *
     * @param lva The result of the live variable analysis
     * @param instrs The set of instructions to simplify
     *
     */
    void simplify(LiveVarsAnal lva, List<Instr> instrs) {

        Register n = pollList(simplifyWorklist, "simplify worklist (simplify)");
        // Register n = simplifyWorklist.poll();

        assert n != null;

        n.type = Type.selected;

        selectStack.push(n);

        Set<Register> adjs = adjacent(n);

        for (Register m : adjs) {
            decrementDegree(m);
        }

    }
    
    /**
     * Check if an instruction i is a move instruction.
     * Notice that the code related to "Instr" is not shared.
     */
    static boolean isMoveInstr(Instr i) {

        if (i instanceof BinOp) {

            BinOp j = (BinOp) i;
            if (j.op == OpType.movq && j.arg1 instanceof Register && j.arg2 instanceof Register) {
                return true;
            }

        }
        return false;
    }

    /**
     * A helper function to add an edge between the two registers r and s in the interference graph.
     */
    void addEdge(Register r, Register s) {

        if (!adjSet.contains(new Pair<>(r, s)) && !r.equals(s)) {

            adjSet.add(new Pair<>(r, s));
            adjSet.add(new Pair<>(s, r));

            if (r.type != Register.Type.precolored) {

                adjListPut(r, s);
                r.degree += 1;

            }

            if (s.type != Register.Type.precolored) {

                adjListPut(s, r);
                s.degree += 1;

            }
        }

    }

    /**
     * A helper function to add the register r to the interference graph.
     */
    void addNode(Register r) {

        registerSet.put(r, r);

        Register k = registerSet.get(r);

        if (k.type == Register.Type.precolored) {

            // precolored.add(r);
            addSet(precolored, k, "precolored (add node)");

        } else {

            k.type = Register.Type.initial;
            addSet(initial, k, "initial (add node)");
            // initial.add(r);

        }

    }

    /** 
     * A helper function to put i and j into the adjacent list.
     */
    void adjListPut(Register i, Register j) {

        Set<Register> child = adjList.get(i);

        if (child == null)
            child = new HashSet<>();

        child.add(j);

        adjList.put(i, child);

    }

    /**
     * A helper function to put i and j into the list of moves.
     */
    void moveListPut(Register i, IntfMove j) {

        Set<IntfMove> child = moveList.get(i);

        if (child == null)
            child = new HashSet<>();

        child.add(j);

        moveList.put(i, child);

    }

    /**
     * Get the alias of a register.
     */
    Register getAlias(Register n) {
        if (n.type == Type.coalesced)
            return getAlias(n.alias);
        return n;
    }

    /**
     * All moves related to the register n.
     */
    Set<IntfMove> nodeMoves(Register n) {
        Set<IntfMove> res = new HashSet<>();
        res.addAll(activeMoves);
        res.addAll(worklistMoves);

        Set<IntfMove> move_n = moveList.get(n);
        if (move_n != null)
            res.retainAll(move_n);
        return res;
    }

    /**
     * Move all registers in nodes to the worklist.
     */
    void enableMoves(Set<Register> nodes) {
        for (Register n : nodes) {
            for (IntfMove m : nodeMoves(n)) {
                if (activeMoves.contains(m)) {
                    // activeMoves.remove(m);
                    removeSetMove(activeMoves, m, "activeMoves (enableMoves)");
                    m.category = Category.worklist;
                    // worklistMoves.add(m);
                    addSetMove(worklistMoves, m, "worklistMoves (enableMoves)");
                }
            }
        }
    }

    /**
     * The set of registers adjacent to n.
     */
    Set<Register> adjacent(Register n) {
        Set<Register> res = new HashSet<>();
        if (adjList.get(n) != null)
            res.addAll(adjList.get(n));
        Set<Register> temp = new HashSet<>();
        temp.addAll(coloredNodes);
        temp.addAll(selectStack);
        res.removeAll(temp);

        return res;
    }

    /**
     * Decrease the degree of the register m.
     */
    void decrementDegree(Register m) {
        int d = m.degree;
        m.degree = d - 1;
        if (d == K) {
            Set<Register> ms = new HashSet<>();
            ms.add(m);
            if (adjacent(m) != null)
                ms.addAll(adjacent(m));
            enableMoves(ms);
            // spillWorklist.remove(m);
            removeQueue(spillWorklist, m, "spill (decrement degree)");

            if (moveRelated(m)) {
                if (m.type != Type.freeze) {
                    m.type = Type.freeze;
                    // freezeWorklist.add(m);

                    addList(freezeWorklist, m, "freeze (decrement degree)");
                }

            } else {
                if (m.type != Type.simplify) {
                    m.type = Type.simplify;
                    // simplifyWorklist.add(m);
                    addList(simplifyWorklist, m, "simplify (decrement degree)");
                }
            }
        }
    }

    /**
     * Combine the two registers.
     */
    void combine(Register u, Register v) {
        if (v.type == Type.freeze) {
            // freezeWorklist.remove(v);
            removeList(freezeWorklist, v, "freeze (combine) 1");
        } else
            // spillWorklist.remove(v);
            removeQueue(spillWorklist, v, "spill (combine)");
        if (v.type != Type.coalesced) {
            v.type = Type.coalesced;

            // for (Register r : adjList.keySet()) {
            // if (adjList.get(r).contains(v)) {
            // for (Register w : adjList.get(r)) {
            // System.out.println("Register " + w + " has type " + w.type);
            // }
            // }
            // }

            // coalescedNodes.add(v);
            addSet(coalescedNodes, v, "coalesced (combine)");
        }
        v.alias = u;

        Set<IntfMove> ul = new HashSet<>();
        ul.addAll(moveList.get(u));
        if (moveList.get(v) != null)
            ul.addAll(moveList.get(v));
        moveList.put(u, ul);

        Set<Register> vl = new HashSet<>();
        vl.add(v);
        enableMoves(vl);

        for (Register t : adjacent(v)) {
            addEdge(t, u);
            decrementDegree(t);
        }
        if (u.degree >= K && u.type == Type.freeze) {
            // freezeWorklist.remove(u);
            removeList(freezeWorklist, u, "freeze (combine) 2");

            u.type = Type.spilled;
            // spillWorklist.add(u);
            addQueue(spillWorklist, u, "spill (combine)");
        }
    }

    /**
     * Add register u to the worklist.
     */
    void addWorklist(Register u) {
        if (u.type != Type.precolored && !moveRelated(u) && u.degree < K) {
            // freezeWorklist.remove(u);
            removeList(freezeWorklist, u, "freeze worklist (addWorklist)");

            u.type = Type.simplify;

            // simplifyWorklist.add(u);
            addList(simplifyWorklist, u, "simplify (addWorklist)");

            // for (Register r : adjList.keySet()) {
            // if (adjList.get(r).contains(u)) {
            // for (Register w : adjList.get(r)) {
            // System.out.println("Register " + w + " has type " + w.type);
            // }
            // }
            // }
        }
    }

    /**
     * Check the boolean ok() for the two registers.
     */
    boolean ok(Register t, Register r) {
        return (t.degree < K) || (t.type == Type.precolored) || (adjSet.contains(new Pair<Register>(t, r)));
    }

    /** A boolean that checks if we need to spill the register.
     */
    boolean conservative(Set<Register> nodes) {
        int k = 0;
        for (Register n : nodes) {
            if (n.degree >= K)
                k++;
        }
        return k < K;
    }

    /**
     * Execute freeze() in the algorithm.
     */
    void freeze() {
        if (!freezeWorklist.isEmpty()) {

            Register r = pollList(freezeWorklist, "freeze work list (freeze)");
            // Register r = freezeWorklist.poll();

            r.type = Type.simplify;
            // simplifyWorklist.add(r);
            addList(simplifyWorklist, r, "simplify (freeze)");

            freezeMoves(r);

        }

    }

    /**
     * Freeze all moves related to r.
     */
    void freezeMoves(Register r) {

        for (IntfMove m : nodeMoves(r)) {

            Register x = registerSet.get(m.x());
            Register y = registerSet.get(m.y());
            Register v = getAlias(y);

            if (getAlias(y).equals(getAlias(r))) {
                v = getAlias(x);
            }

            // activeMoves.remove(m);
            removeSetMove(activeMoves, m, "active moves (freezeMoves)");
            // frozenMoves.add(m);
            addSetMove(frozenMoves, m, "freeze moves (freezeMoves)");
            m.category = IntfMove.Category.frozen;

            if (v.type == Type.freeze && nodeMoves(v).isEmpty()) {
                removeList(freezeWorklist, v, "freeze worklist (freezeMoves)");
                // freezeWorklist.remove(v);

                v.type = Type.simplify;

                // simplifyWorklist.add(v);
                addList(simplifyWorklist, v, "simplify worklist (freezeMoves)");
            }

        }
    }

    /**
     * Select registers to spill.
     */
    void selectSpill() {

        Register m = pollList(spillWorklist, "spill worklist (select spill)");
        // Register m = spillWorklist.poll();
        // selected using heuristic TODO improve

        m.type = Type.simplify;

        addList(simplifyWorklist, m, "simplify worklist (select spill)");
        // simplifyWorklist.add(m);

        freezeMoves(m);

    }

    /** 
     * Assign colors to the registers in the select stack.
     */
    void assignColors() {
        while (!selectStack.empty()) {

            Register n = selectStack.pop();

            Set<regNames> okColors = new HashSet<regNames>();
            okColors.addAll(Register.all_regs);

            if (adjList.get(n) != null) {

                for (Register w : adjList.get(n)) {

                    Register alias = getAlias(w);
                    Type type = alias.type;

                    if (type == Type.colored) {

                        okColors.remove(colorMap.get(alias.getArgName()));
                    } else if (type == Type.precolored) {

                        okColors.remove(alias.getRegNames());
                    } else if (type == null) {
                        String argName = alias.getArgName();
                        regNames color = colorMap.get(argName);
                        if (color != null) {
                            alias.type = Type.colored;
                            okColors.remove(color);
                        }
                    } else {
                    }

                }
            }

            if (okColors.isEmpty()) {
                n.type = Type.spilled;
                addSet(spilledNodes, n, "spilledNodes(assign colors)");
                // spilledNode.add(n);

            } else {
                n.type = Type.colored;

                addSet(coloredNodes, n, "coloredNodes(n)");
                // coloredNodes.add(n);
                regNames r = okColors.iterator().next();
                colorMap.put(n.getArgName(), r);

            }
        }

        for (Register n : coalescedNodes) {

            if (colorMap.get(getAlias(n).getArgName()) != null) {
                colorMap.put(n.getArgName(), colorMap.get(getAlias(n).getArgName()));
            } else {
                colorMap.put(n.getArgName(), getAlias(n).getRegNames());
            }


        }

    }

    /**
     * Rewrite the whole program and do another round of LVA on the program after some registers are spilled.
     * @param ra The register allocation program to get the memory offset from.
     * @param lva The information of the old live variable analysis.
     * @param instrs The instructions to process (conduct register allocation) and to modify.
     */
    void rewriteProgram(RegisterAlloc ra, LiveVarsAnal lva, List<Instr> instrs) {

        for (Register r : spilledNodes) {

            int n = ra.newMemoryOffset();

            for (int i = 0; i < instrs.size(); ++i) {

                Instr instr = instrs.get(i);

                Mem m = ra.getMemory(instr, n);


                if (lva.use(instr).contains(r) && lva.def(instr).contains(r)) {
                    Register r0 = new Register(Factory.tempFactory());
                    instrs.add(i, new BinOp(OpType.movq, m, r0));
                    instrs.add(i + 2, new BinOp(OpType.movq, r0, m));
                    i += 2;
                    lva.useReplace(instr, r, r0);
                    lva.defReplace(instr, r, r0);
                }

                else if (lva.use(instr).contains(r)) {
                    Register r0 = new Register(Factory.tempFactory());
                    instrs.add(i, new BinOp(OpType.movq, m, r0));
                    i++;
                    lva.useReplace(instr, r, r0);
                    // replace use of r in this instruction with r0

                } else if (lva.def(instr).contains(r)) {
                    Register r0 = new Register(Factory.tempFactory());
                    instrs.add(i + 1, new BinOp(OpType.movq, r0, m));
                    i++;
                    lva.defReplace(instr, r, r0);
                    // replace def of r in this instruction with r0

                }
            }
            
        }

    }

    /**
     * Execute coalesce() in the algorithm.
     */
    void coalesce() {
        if (!worklistMoves.isEmpty()) {
            IntfMove m = worklistMoves.iterator().next();
            Register x = registerSet.get(m.x());
            Register y = registerSet.get(m.y());
            x = getAlias(x);
            y = getAlias(y);

            Pair<Register> uv;
            if (y.type == Type.precolored)
                uv = new Pair<>(y, x);
            else
                uv = new Pair<>(x, y);
            // worklistMoves.remove(m);
            removeSetMove(worklistMoves, m, "worklistMoves (coalesce)");

            if (uv.first.equals(uv.second)) {
                // coalescedMoves.add(m);
                addSetMove(coalescedMoves, m, "coalescedMoves 1 (coalesce)");
                m.category = Category.coalesced;
                addWorklist(uv.first);
            } else if (uv.second.type == Type.precolored || adjSet.contains(uv)) {
                // constrainedMoves.add(m);
                addSetMove(constrainedMoves, m, "constrainedMoves (coalesce)");
                m.category = Category.constrained;
                addWorklist(uv.first);
                addWorklist(uv.second);
            } else {
                boolean is_ok = true;
                for (Register t : adjacent(uv.second)) {
                    if (!ok(t, uv.first)) {
                        is_ok = false;
                    }
                }
                Set<Register> adj_uv = new HashSet<>();
                if (adjacent(uv.first) != null)
                    adj_uv.addAll(adjacent(uv.first));
                if (adjacent(uv.second) != null)
                    adj_uv.addAll(adjacent(uv.second));

                if ((uv.first.type == Type.precolored && is_ok)
                        || (uv.first.type != Type.precolored && conservative(adj_uv))) {
                    // coalescedMoves.add(m);
                    addSetMove(coalescedMoves, m, "coalescedMoves 2 (coalesce)");
                    m.category = Category.coalesced;
                    combine(uv.first, uv.second);
                    addWorklist(uv.first);
                } else {
                    m.category = Category.active;
                    // activeMoves.add(m);
                    addSetMove(activeMoves, m, "activeMoves (coalesce)");
                }

            }
        }
    }

    // Add the register reg in the worklist. info is used to print this addition as an log.
    void addList(Queue<Register> worklist, Register reg, String info) {
        // System.out.println(info + "list " + worklist + " add " + reg);
        worklist.add(reg);
    }

    // Remove the register reg from the worklist. info is used to print this operation as an log.
    void removeList(Queue<Register> worklist, Register reg, String info) {
        // System.out.println(info + "list " + worklist + " remove " + reg);
        worklist.remove(reg);
    }

    // Poll the newest register reg from the worklist. info is used to print this operation as an log.
    Register pollList(Queue<Register> worklist, String info) {
        Register reg = worklist.poll();
        // System.out.println(info + "list " + worklist + " poll " + reg);
        return reg;
    }

    // Add the register reg in the set. info is used to print this addition as an log.
    void addSet(Set<Register> nodes, Register reg, String info) {
        // System.out.println(info + "set " + nodes + " add " + reg);
        nodes.add(reg);
    }

    // Remove reg from the set. info is used to print this operation as an log.
    void removeSet(Set<Register> nodes, Register reg, String info) {
        // System.out.println(info + "set " + nodes + " remove " + reg);
        nodes.remove(reg);
    }

    // Add the register reg in the worklist. info is used to print this operation as an log.
    void addAllSet(Set<Register> nodes, Set<Register> regs, String info) {
        // System.out.println(info + "set " + nodes + " add all " + regs);
        nodes.addAll(regs);
    }

    // Add a move to the set of moves. info is used to print this operation as an log.
    void addSetMove(Set<IntfMove> nodes, IntfMove reg, String info) {
        // System.out.println(info + "set " + nodes + " add " + reg);
        nodes.add(reg);
    }

    // Remove a move from the set of moves. info is used to print this operation as an log.
    void removeSetMove(Set<IntfMove> nodes, IntfMove reg, String info) {
        // System.out.println(info + "set " + nodes + " remove " + reg);
        nodes.remove(reg);
    }

    // Add a set of moves to the set of moves. info is used to print this operation as an log.
    void addAllSetMove(Set<IntfMove> nodes, Set<IntfMove> regs, String info) {
        // System.out.println(info + "set " + nodes + " add all " + regs);
        nodes.addAll(regs);
    }

     // Remove a set of moves from the set of moves. info is used to print this operation as an log.
    void removeAllSet(Set<Register> nodes, Set<Register> regs, String info) {
        // System.out.println(info + "set " + nodes + " remove all " + regs);
        nodes.removeAll(regs);
    }

     // Add a register reg to the priority queue. info is used to print this operation as an log.
    void addQueue(PriorityQueue<Register> worklist, Register reg, String info) {
        // System.out.println(info + "list " + worklist + " add " + reg);
        worklist.add(reg);
    }

    // Remove a register reg from the priority queue. info is used to print this operation as an log.
    void removeQueue(PriorityQueue<Register> worklist, Register reg, String info) {
        // System.out.println(info + "list " + worklist + " remove " + reg);
        worklist.remove(reg);
    }

}
