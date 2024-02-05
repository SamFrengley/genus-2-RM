This directory contains some simple test scripts which one may run to either
- convince oneself that our (complicated) equations are valid, or
- get to terms with the minimization algorithm.

In particular:
- `F_zghrs_analytic-RM.m` gives a heuristic test for our equations by using the `AnalyticJacobian` machinery in `Magma` (see the [Magma Documentation](http://magma.maths.usyd.edu.au/magma/handbook/text/1571)). The basic test is to specialise at some complex numbers and use this machine.
  - NB. if you think you have a counter-example, try increasing the precision of the `ComplexField`.
- `f_abc_analytic-RM.m` is the same, except it uses the equations in $a,b,c$ as given in the corollaries.
- `minimize-conics.m` gives examples for how to run `MinimizationSearch`.
  - NB. if working on a non-unix system comment out the `Pipe` command (which just pauses the running so you can read the previous output).