# Compilers Coding Sample
This directory contains a snippet of our compilers project, specifically the graph coloring register allocation algorithm (which I mostly wrote) serving an optimization for our compilers. Thanks for this piece of code and other optimizations we did including loop invariant code motion and dead code elimination, our compiler wins the "best compiler award" in Cornell's undergraduate compiler's class. 

All content is in "pa1\_student/src/zw494". Notice that the "Optimization" directory contains the register allocation algorithm. It depends on two directories called "CFG", which defines the control flow graph of our compilers, and "Assembly", which defines the Register class and other data structures that are the targets of our register allocation algorithm. I am not sharing these directories.

"RegisterAlloc.java" is the gateway for the algorithm. "IntfGraphTest.java" is the main implementation of the interference graph as well as the graph coloring algorithm. "DataFlowAnal.java" and the "LiveVarsAnal.java" are implementations of the live variable analysis. 
