# Minisat-instrumented with resolution graph tracing

Run minisat as usual. Flag in beginning of `SolverTypes.h` turns tracing on or off
(compile-time flag to allow tracing to be optimized away if not used).

Not working:
* Minimization mode 2
* DPLL mode (not understood or verified)

Working:
* Hopefully everything else

Comments in code explain format (look for `REFUTATION_TRACING` in `SolverTypes.h`
and `Solver.cc`).
