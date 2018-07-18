#!/usr/bin/python

import sys;

if len(sys.argv) < 2:
    print "usage: sz.py <k> <N>"
    exit(1);

from z3 import *;

k = int(sys.argv[1]);
N = int(sys.argv[2]);

for n in range(k, N):
    z3input = "(declare-const size Int)\n";

    sizestring = "(assert (= size (+";
    for i in range(0, n):
        z3input += "(declare-const x%d Int)\n" % i;
        z3input += "(assert (< x%d 2))\n" % i;
        z3input += "(assert (>= x%d 0))\n" % i;
        sizestring += " x%d" % i;
    
    sizestring += ")))\n";
    z3input += sizestring;

    for i in range(0, n - k + 1):
        d = 1;
        while i + (k - 1) * d < n:
            constraint = "(assert (> %d (+" % k;
            for j in range(0, k):
                constraint += " x%d" % (i + j * d);
            constraint += ")))\n";
            z3input += constraint;
            d += 1;

    z3 = Optimize();
    z3.from_string(z3input);

    size = Int('size');
    h = z3.maximize(size);
    
    print "sz(%d,%d): " % (k,n);
    print "check: ", z3.check();
    print "upper: ", z3.upper(h);
    #print "model: ", z3.model();
