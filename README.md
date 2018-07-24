Small Numbers
=============

This repository is a shrine to small numbers.

Specifically, we are interested in concrete values of combinatorial
functions with small parameters, especially those in the world of
extremal combinatorics and Ramsey theory.

Many people focus on the asymptotic behavior of these functions when
the parameters are arbitrarily large. Instead, we focus on the details
of small cases. Interesting things happen in these small values.

Here are a few such functions:

* [**Szemerédi Numbers:**](sz) The number sz(k,n) is the size of the
  largest subset A of {1,...,n} that does not contain an arithmetic
  progression of length k.

* [**van der Waerden Numbers:**](vdw) The number vdw(t,k) is the smallest
  n such that every t-coloring of {1,...,n} contains a monochromatic
  arithmetic progression of length k. There are off-diagonal versions
  of these numbers, too.

* [**Erdős Discrepancy Numbers:**](disc) The number disc(C) is the smallest
  n such that every sequence {x_1,...,x_n} with each x_i in {-1,+1} has
  _discrepancy_ at least C. That is, there exist integers d and k with
  d*k <= n where the absolute value of the sum x_d + x_2d + ... + x_kd
  is at least C. Only disc(2) and disc(3) are known.

Approach
--------

We collect results from the mathematical literature to create a list
of the known values and bounds for these small numbers.

We try to reproduce these results using "simple" approaches.

One such simple approach is to use a SAT solver. In our case, we will
use the [Z3 Satisfiability Modulo Theory (SMT) solver](https://github.com/Z3Prover/z3).
There are some very powerful proof techniques built into this tool, and
we can use them to find bounds and _prove_ their value. We provide these
proofs for later verification when possible.

Another simple approach is to use simple backtrack search with some
basic constraint solving methods. These can sometimes provide easier
to understand approaches to these calculations, but also to enumerate
all extremal solutions.

License
-------

Small Numbers is available as open-source under the MIT License. See
[LICENSE.md](LICENSE.md) for more details.
