van der Waerden Numbers
=======================

For an integer _k_ > 1, a _k_-term arithmetic progression
(_k_-AP for short) is a sequence _x_(1),...,_x_(k) of integers
such that there is a constant _d_ where _d_ = _x_(_i_ + 1) - _x_(i)
for all _i_ in {1,...,_k_-1}.

For integers _k_(1),...,_k_(_t_), the _t_-color **van der Waerden number**
vdw(_k_(1),...,_k_(_t_)) is the minimum number _N_ such that every coloring
_c_ of {1,...,_N_} using colors {1,...,_t_} contains a _k_(_i_)-AP of color _i_
for some color. We call these _monochromatic_ APs.

For the input values, we refer to a coloring that avoids these monochromatic APs
as a _valid_ coloring.

Computing
---------

To compute van der Waerden numbers, we have the following approaches.

### Z3 SMT Solver

Using the [Z3 Satisfiability Modulo Theory (SMT) Solver](https://github.com/Z3Prover/z3),
we can find existence of valid colorings for N below the van der Waerden
number, and prove nonexistence of valid colorings beyond the van der
Waerden number.

We use Python scripts to generate the constraint systems for Z3, and use
the Python API to solve these systems. If you prefer to instead verify
the systems that are already created, you can see the `vdw-*.z3` files in
the `data` folder.

For two colors, use `vdw-2.py k1 k2` to determine the van der Waerden number
vdw(k1,k2). Optionally, use `vdw-2.py k1 k2 n` to start the computation at
the value _n_. This approach creates an integer program where each position
_i_ in {1,...,_n_} has a 0-1 variable _x_(_i_) and we guarantee the APs are
not monochromatic by bounding their sum to be at least 1 or at most k1-1.
This is more efficient than the approach required for three or more colors.

For three or more colors, use `vdw-t.py t k1 ... kt <n>` to determine the
van der Waerden number vdw(k1,...,kt); optionally start the computation at
the value _n_. This approach uses an integer program where each position
_i_ in {1,...,_n_} has _t_ 0-1 variables _x_(_i_,_c_) where _c_ is a color
value in {0,...,_t_-1}. We ensure the sum of _x_(_i_,0) + ... + _x_(_i_,_t_-1)
is exactly 1 to guarantee a unique color on each position, and bound the
sum across each AP is one below its length in that color.

Results
-------

In the tables below, we list the van der Waerden numbers whose exact
values are known. We reference the original prover by marking the
reference next to the value. We use **TODO** to mark numbers that
are not verified by the Small Numbers project.

### Two Colors

| k1 | k2 | vdw(k1,k2) | Proven By       |
|----|----|------------|-----------------|
| 3  | 3  | 9          | [C70]           |
| 3  | 4  | 18         | [C70]           |
| 3  | 5  | 22         | [C70]           |
| 3  | 6  | 32         | [C70]           |
| 3  | 7  | 46         | [C70]           |
| 3  | 8  | 58         | [BO79]          |
| 3  | 9  | 77         | [BO79]          |
| 3  | 10 | 97         | [BO79]          |
| 3  | 11 | 114        | [LRC05]         |
| 3  | 12 | 135        | [LRC05]         |
| 3  | 13 | 160        | [LRC05]         |
| 3  | 14 | 186        | [K06]   **TODO**|
| 3  | 15 | 218        | [K06]   **TODO**|
| 3  | 16 | 238        | [K06]   **TODO**|
| 3  | 17 | 279        | [A10]   **TODO**|
| 3  | 18 | 312        | [A10]   **TODO**|
| 3  | 19 | 349        | [AKS14] **TODO**|
| 4  | 4  | 35         | [C70]           |
| 4  | 5  | 55         | [C70]           |
| 4  | 6  | 73         | [BO79]          |
| 4  | 7  | 109        | [B83]           |
| 4  | 8  | 146        | [K06]           |
| 4  | 9  | 309        | [A12]   **TODO**|
| 5  | 5  | 178        | [SS78]          |
| 5  | 6  | 206        | [K06]   **TODO**|
| 5  | 7  | 260        | [A13]   **TODO**|
| 6  | 6  | 1,132      | [KP08]  **TODO**|

### Three Colors

| k1 | k2 | k3 | vdw(k1,k2,k3) | Proven By         |
|----|----|----|---------------|-------------------|
|  2 |  3 |  3 |       14      | [B74]             |
|  2 |  3 |  4 |       21      | [B74]             |
|  2 |  3 |  5 |       32      | [B74]             |
|  2 |  3 |  6 |       40      | [B74]             |
|  2 |  3 |  7 |       55      | [LRC05]           |
|  2 |  3 |  8 |       72      | [K06]             |
|  2 |  3 |  9 |       90      | [A09]             |
|  2 |  3 | 10 |      108      | [A09]             |
|  2 |  3 | 11 |      129      | [A09]             |
|  2 |  3 | 12 |      150      | [A09]    **TODO** |
|  2 |  3 | 13 |      171      | [A09]    **TODO** |
|  2 |  3 | 14 |      202      | [K12]    **TODO** |
|  2 |  4 |  4 |       40      | [B74]             |
|  2 |  4 |  5 |       71      | [B74]             |
|  2 |  4 |  6 |       83      | [LRC05]           |
|  2 |  4 |  7 |      119      | [K06]    **TODO** |
|  2 |  4 |  8 |      157      | [K12]    **TODO** |
|  2 |  5 |  5 |      180      | [A09]    **TODO** |
|  2 |  5 |  6 |      246      | [K12]    **TODO** |
|  3 |  3 |  3 |       27      | [C70]             |
|  3 |  3 |  4 |       51      | [BO79]            |
|  3 |  3 |  5 |       80      | [LRC05]           |
|  3 |  3 |  6 |      107      | [A09]    **TODO** |
|  3 |  4 |  4 |       89      | [LRC05]           |
|  4 |  4 |  4 |      293      | [K12]    **TODO** |

### Four Colors

| k1 | k2 | k3 | k4 | vdw(k1,k2,k3,k4) | Proven By        |
|----|----|----|----|------------------|------------------|
|  2 |  2 |  3 |  3 |         17       | [B74]            |
|  2 |  2 |  3 |  4 |         24       | [B74]            |
|  2 |  2 |  3 |  5 |         43       | [B74]            |
|  2 |  2 |  3 |  6 |         48       | [LRC05]          |
|  2 |  2 |  3 |  7 |         65       | [LRC05]          |
|  2 |  2 |  3 |  8 |         83       | [A09]            |
|  2 |  2 |  3 |  9 |         99       | [A09]            |
|  2 |  2 |  3 | 10 |        119       | [A09]   **TODO** |
|  2 |  2 |  3 | 11 |        141       | [S19]   **TODO** |
|  2 |  2 |  4 |  4 |         53       | [B74]            |
|  2 |  2 |  4 |  5 |         75       | [A09]            |
|  2 |  2 |  4 |  6 |         93       | [A09]   **TODO** |
|  2 |  2 |  4 |  7 |        143       | [K12]   **TODO** |
|  2 |  3 |  3 |  3 |         40       | [B74]            |
|  2 |  3 |  3 |  4 |         60       | [LRC05]          |
|  2 |  3 |  3 |  5 |         86       | [A09]   **TODO** |
|  3 |  3 |  3 |  3 |         76       | [BO79]  **TODO** |

### Five Colors

| k1 | k2 | k3 | k4 | k5 | vdw(k1,k2,k3,k4,k5) | Proven By        |
|----|----|----|----|----|---------------------|------------------|
|  2 |  2 |  2 |  3 |  3 |            20       | [LRC05]          |
|  2 |  2 |  2 |  3 |  4 |            29       | [A09]            |
|  2 |  2 |  2 |  3 |  5 |            44       | [A09]            |
|  2 |  2 |  2 |  3 |  6 |            56       | [A09]            |
|  2 |  2 |  2 |  3 |  7 |            72       | [A09]   **TODO** |
|  2 |  2 |  2 |  3 |  8 |            88       | [A09]            |
|  2 |  2 |  2 |  3 |  9 |           107       | [K12]   **TODO** |
|  2 |  2 |  2 |  4 |  4 |            54       | [A09]            |
|  2 |  2 |  2 |  4 |  5 |            79       | [A09]   **TODO** |
|  2 |  2 |  2 |  4 |  6 |           101       | [K12]   **TODO** |
|  2 |  2 |  3 |  3 |  3 |            41       | [LRC05]          |
|  2 |  2 |  3 |  3 |  4 |            63       | [A09]   **TODO** |

References
----------

[A09] Tanbir Ahmed,
      "Some new van der Waerden numbers and some van der Waerden-type numbers"
      _Integers_ **9**:
      (2009) A6.

[A10] Tanbir Ahmed,
      "Two new van der Waerden numbers w(2;3,17) and w(2;3,18)"
      _Integers_ **10**:
      (2010) pp. 369–377.

[AKS14] Tanbir Ahmed, Oliver Kullmann, and Hunter Snevily,
        "On the van der Waerden numbers w(2;3,t)".
        _Discrete Appl. Math._ **174**:
        (2014) pp. 27–51.

[BO79] Michael D. Beeler and Patrick E O'Neil,
       "Some new van der Waerden numbers"
       _Discrete Math._ **28** (2):
       (1979) pp. 135–146.

[B74] T. C. Brown
      "Some new van der Waerden numbers (preliminary report)".
      _Notices of the American Mathematical Society_ **21**
      (1974) A–432.

[C70] Vašek Chvátal. "Some unknown van der Waerden numbers"
      In Guy, Richard; Hanani, Haim; Sauer, Norbert; _et al._
      _Combinatorial Structures and Their Applications_
      (1970) pp. 31–33.

[K06] Michal Kouril,
      _A Backtracking Framework for Beowulf Clusters with an Extension to Multi-Cluster Computation and Sat Benchmark Problem Implementation_
      (Ph.D. thesis). University of Cincinnati (2006).

[K12] Michal Kouril
      "Computing the van der Waerden number W(3,4)=293"
      _Integers_ **12**:
      (2012) A46.

[KP08] Michal Kouril and Jerome L. Paul,
       "The Van der Waerden Number W(2,6) is 1132"
       _Experimental Mathematics_ **17** (1):
       (2008) pp. 53–61.

[LRC05] Bruce Landman, Aaron Robertson, and Clay Culver,
        "Some New Exact van der Waerden Numbers"
        _Integers_ **5** (2): 
        (2005) A10.

[S09] Pascal Schweitzer,
      _Problems of Unknown Complexity, Graph isomorphism and Ramsey theoretic numbers_ (Ph.D. thesis)
      U. des Saarlandes (2009).
