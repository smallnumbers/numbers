Green-Tao Numbers
=================

For an integer _k_ > 1, a _k_-term arithmetic progression
(_k_-AP for short) is a sequence _x_(1),...,_x_(k) of integers
such that there is a constant _d_ where _d_ = _x_(_i_ + 1) - _x_(i)
for all _i_ in {1,...,_k_-1}.

The Green-Tao Theorem states that the primes contain arithmetic
progressions of any length. But how quickly do we find arithmetic
progressions of a given length?

For an integer _k_ &ge; 3, the **Green-Tao Number** gt(_k_) is the
minimum prime _p_ such that there exists a _k_-AP of primes ending
at _p_.

Computing
---------

The algorithm is very simple. It takes two parts, each of which is
not optimized at all.

1. Compute a set of prime numbers. Uses the sieve of Eratosthenes.
   **TODO:** Improvements can be made here to reduce the memory
   footprint by running the sieve in smaller interval windows.

2. For each prime _p_, determine the longest AP ending at that prime.
   Simply test, for each smaller prime _q_, if the difference _p_ - _q_
   provides an AP of prime numbers. Uses binary search to determine
   if the value is prime. **TODO:** This could use a hashtable to reduce
   lookup time, or use a primality test to completely remove the memory
   requirement of storing all prime numbers to a certain value.

Results
-------

Here are the first few Green-Tao numbers, along with the progression
that demonstrates gt(_k_) &le; _p_:

| k  | gt(k)  | Set                                                                                                   |
|----|--------|-------------------------------------------------------------------------------------------------------|
| 3  | 7      | {3,5,7}                                                                                               |
| 4  | 23     | {5,11,17,23}                                                                                          |
| 5  | 29     | {5,11,17,23,29}                                                                                       |
| 6  | 157    | {7, 37, 67 , 97, 127, 157}                                                                            |
| 7  | 907    | {7, 157, 307, 457, 607, 757, 907}                                                                     |
| 8  | 1669   | { 199, 409, 619, 829, 1039, 1249, 1459, 1669}                                                         |
| 9  | 1879   | {199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879}                                                    |
| 10 | 2089   | {199, 409, 619, 829, 1039, 1249, 1459, 1669, 1879, 2089}                                              |
| 11 | 249037 | {110437, 124297, 138157, 152017, 165877, 179737, 193597, 207457, 221317, 235177, 249037}              |
| 12 | 262897 | {110437, 124297, 138157, 152017, 165877, 179737, 193597, 207457, 221317, 235177, 249037, 262897}      |
| 13 | 725663 | {4943, 65003, 125063, 185123, 245183, 305243, 365303, 425363, 485423, 545483, 605543, 665603, 725663} |
