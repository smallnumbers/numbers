#!/usr/bin/python

import sys;
import os;

if len(sys.argv) < 2:
    print "usage: vdw.py <t> <k> [n_min]"
    exit(1);

from z3 import *;

t = int(sys.argv[1]);
k = int(sys.argv[2]);

n = t * k;
if len(sys.argv) > 3:
    n = int(sys.argv[3]);

def variable_str(i,j):
    return "x%dc%d" % (i,j);

i = 0;

variables = "";
constraints = "";
while True:
    # Add variables
    unique_constraint = "(assert (= 1 (+";
    for j in range(0,t):
        variable = variable_str(i,j);
        variables += "(declare-const %s Int)\n" % variable;
        variables += "(assert (>= %s 0))\n" % variable;
        variables += "(assert (<= %s 1))\n" % variable;
        unique_constraint += " " + variable;

    unique_constraint += ")))\n";
    variables += unique_constraint;

    d = 1;
    while i - (k - 1) * d >= 0:
        for j in range(0,t):
            monocolor_constraint = "(assert (>= %d (+" % (k - 1);
            for p in range(0,k):
                monocolor_constraint += " " + variable_str(i - p * d, j);
            monocolor_constraint += ")))\n";
            constraints += monocolor_constraint;
        d += 1;
 
    i += 1;
    if i < n:
        continue;

    solve_file = open("vdw-t%d-k%d-n%d.z3" % (t,k,i), "w");
    solve_file.write(variables + constraints);
    solve_file.close();

    z3 = Solver();
    z3.from_string(variables + constraints);

    print "vdw for t=%d, k=%d, n=%d:\n" % (t,k,i);
    check = z3.check();
    print "check: ", check;

    if check == sat:
        to_delete = "vdw-t%d-k%d-n%d.z3" % (t,k,i-1);
        if os.path.isfile(to_delete):
            os.remove(to_delete);
    else:
        k += 1;
        constraints = "";
        for ii in range(0,i):
            d = 1;
            while ii - (k - 1) * d >= 0:
                for j in range(0,t):
                    monocolor_constraint = "(assert (>= %d (+" % (k - 1);
                    for p in range(0,k):
                        monocolor_constraint += " " + variable_str(i - p * d, j);
                    monocolor_constraint += ")))\n";
                    constraints += monocolor_constraint;
                d += 1;

