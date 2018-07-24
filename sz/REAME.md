Szemerédi Numbers
=================

For an integer _k_ > 1, a _k_-term arithmetic progression
(_k_-AP for short) is a sequence _x_(1),...,_x_(k) of integers
such that there is a constant _d_ where _d_ = _x_(_i_ + 1) - _x_(i)
for all _i_ in {1,...,_k_-1}.

For integers _n_ and _k_, the **Szemerédi Number** sz(_n_,_k_) is the
maximum size of a _k_-AP-free set in {1,...,_n_}.

These are named after Szemerédi's Theorem, which proves that any
(infinite) set of natural numbers with positive density contains
arbitrarily long arithmetic progressions. The term was coined in [R16].

Computing
---------

To compute Szemerédi numbers, we use two approaches.

### Z3 SMT Solver

Using the [Z3 Satisfiability Modulo Theory (SMT) Solver](https://github.com/Z3Prover/z3),
we can maximize an integer program whose feasible solutions are _k_-AP-free
sets. Due to the solver's ability to use the linear relaxation, this approach
works very well for larger values of _k_.

We use Python scripts to generate the constraint systems for Z3, and use
the Python API to solve these systems. If you prefer to instead verify
the systems that are already created, you can see the `sz-*.z3` files in
the `data` folder.

To generate and run the scripts, run `sz.py <N>` where `N` is maximum
value of _n_ you want to compute. The script will compute all numbers
up to that value. It will create a space-separated table at `data/sz.csv`
that is re-used by later runs so you do not need to recompute values.

### Backtrack Search

A simple backtrack search is implemented in C as `sz.c`. Compile it by running
`make` and run it with the command

```
sz <minN> <maxN> [maxK]
```

And it will compute all numbers sz(_n_,_k_) with _n_ between `minN` and `maxN`
and _k_ at most `maxK`.

Results
-------

In the table below, we list known Szemerédi numbers, limiting k to at most 10.

| n  | k=3 | k=4 | k=5 | k=6 | k=7 | k=8 | k=9 | k=10 |
|----|-----|-----|-----|-----|-----|-----|-----|------|
| 4  | 3   |     |     |     |     |     |     |      |
| 5  | 4   | 4   |     |     |     |     |     |      |
| 6  | 4   | 5   | 5   |     |     |     |     |      |
| 7  | 4   | 5   | 6   | 6   |     |     |     |      |
| 8  | 4   | 6   | 7   | 7   | 7   |     |     |      |
| 9  | 5   | 7   | 8   | 8   | 8   | 8   |     |      |
| 10 | 5   | 8   | 8   | 9   | 9   | 9   | 9   |      |
| 11 | 6   | 8   | 9   | 9   | 10  | 10  | 10  | 10   |
| 12 | 6   | 8   | 10  | 10  | 11  | 11  | 11  | 11   |
| 13 | 7   | 9   | 11  | 11  | 12  | 12  | 12  | 12   |
| 14 | 8   | 9   | 12  | 12  | 12  | 13  | 13  | 13   |
| 15 | 8   | 10  | 12  | 13  | 13  | 13  | 14  | 14   |
| 16 | 8   | 10  | 13  | 13  | 14  | 14  | 15  | 15   |
| 17 | 8   | 11  | 14  | 14  | 15  | 15  | 16  | 16   |
| 18 | 8   | 11  | 15  | 15  | 16  | 16  | 16  | 17   |
| 19 | 8   | 12  | 16  | 16  | 17  | 17  | 17  | 17   |
| 20 | 9   | 12  | 16  | 17  | 18  | 18  | 18  | 18   |
| 21 | 9   | 13  | 16  | 17  | 18  | 19  | 19  | 19   |
| 22 | 9   | 13  | 16  | 18  | 19  | 19  | 20  | 20   |
| 23 | 9   | 14  | 16  | 19  | 20  | 20  | 21  | 21   |
| 24 | 10  | 14  | 17  | 20  | 21  | 21  | 22  | 22   |
| 25 | 10  | 15  | 18  | 21  | 22  | 22  | 22  | 23   |
| 26 | 11  | 15  | 18  | 22  | 23  | 23  | 23  | 24   |
| 27 | 11  | 16  | 19  | 22  | 24  | 24  | 24  | 25   |
| 28 | 11  | 17  | 20  | 22  | 24  | 25  | 25  | 26   |
| 29 | 11  | 17  | 21  | 23  | 25  | 25  | 26  | 26   |
| 30 | 12  | 18  | 21  | 23  | 26  | 26  | 27  | 27   |
| 31 | 12  | 18  | 22  | 23  | 27  | 27  | 28  | 28   |
| 32 | 13  | 18  | 22  | 24  | 28  | 28  | 28  | 29   |
| 33 | 13  | 19  | 23  | 25  | 29  | 29  | 29  | 30   |
| 34 | 13  | 20  | 24  | 25  | 30  | 30  | 30  | 30   |
| 35 | 13  | 20  | 24  | 26  | 30  | 31  | 31  | 31   |
| 36 | 14  | 20  | 25  | 27  | 31  | 31  | 32  | 32   |
| 37 | 14  | 21  | 26  | 28  | 32  | 32  | 33  | 33   |
| 38 | 14  | 21  | 27  | 28  | 33  | 33  | 34  | 34   |
| 39 | 14  | 21  | 28  | 29  | 34  | 34  | 34  | 35   |
| 40 | 15  | 22  | 28  | 30  | 35  | 35  | 35  | 36   |
| 41 | 16  | 22  | 29  | 31  | 36  | 36  | 36  | 36   |
| 42 | 16  | 22  | 30  | 31  | 36  | 37  | 37  | 37   |
| 43 | 16  | 23  | 31  | 31  | 36  | 37  | 38  | 38   |
| 44 | 16  | 23  | 32  | 32  | 36  | 38  | 39  | 39   |
| 45 | 16  | 24  | 32  | 33  | 36  | 39  | 40  | 40   |
| 46 | 16  | 24  | 32  | 34  | 37  | 40  | 40  | 41   |
| 47 | 16  | 24  | 32  | 34  | 37  | 41  | 41  | 42   |
| 48 | 16  | 25  | 32  | 35  | 38  | 42  | 42  | 42   |
| 49 | 16  | 25  | 33  | 36  | 38  | 43  | 43  | 43   |
| 50 | 16  | 26  | 33  | 37  | 39  | 44  | 44  | 44   |

In the table below, we list the extremal examples for 3-AP-free sets.
We only include values _n_ where sz(_n_,3) &gt; sz(_n_-1,3).

| n  | k | sz(n,k) | solution                                          |
|----|---|---------|---------------------------------------------------|
| 4  | 3 | 3       | `1 2 4`                                           |
| 5  | 3 | 4       | `1 2 4 5`                                         |
| 9  | 3 | 5       | `1 2 4 8 9`                                       |
| 11 | 3 | 6       | `1 2 4 5 10 11`                                   |
| 13 | 3 | 7       | `1 2 4 5 10 11 13`                                |
| 14 | 3 | 8       | `1 2 4 5 10 11 13 14`                             |
| 20 | 3 | 9       | `1 2 6 7  9 14 15 18 20`                          |
| 24 | 3 | 10      | `1 2 5 7 11 16 18 19 23 24`                       |
| 26 | 3 | 11      | `1 2 5 7 11 16 18 19 23 24 26`                    |
| 30 | 3 | 12      | `1 3 4 8  9 11 20 22 23 27 28 30`                 |
| 32 | 3 | 13      | `1 2 4 8  9 11 19 22 23 26 28 31 32`              |
| 36 | 3 | 14      | `1 2 4 8  9 13 21 23 26 27 30 32 35 36`           |
| 40 | 3 | 15      | `1 2 4 5 10 11 13 14 28 29 31 32 37 38 40`        |
| 41 | 3 | 16      | `1 2 4 5 10 11 13 14 28 29 31 32 37 38 40 41`     |

References
----------

[R16] Steve Butler, Craig Erickson, Leslie Hogben, Kirsten Hogenson,
      Lucas Kramer, Richard L Kramer, Jephian Chin-Hung Lin,
      Ryan R Martin, Derrick Stolee, Nathan Warnberg, and Michael Young,
      "Rainbow Arithmetic Progressions"
      _Journal of Combinatorics_ **7** (4):
     (2016) pp. 595-626.