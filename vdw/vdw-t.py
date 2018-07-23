#!/usr/bin/python

import sys;
import os;

if len(sys.argv) < 2:
	print "usage: vdw.py <t> <k1> ... <kt>"
	exit(1);

t = int(sys.argv[1]);

if len(sys.argv) < 2 + t:
	print "usage: vdw.py <t> <k1> ... <kt>"
	exit(1);
	
from z3 import *;
	
k = [int(sys.argv[i + 2]) for i in range(t)];

n = sum([k[i] - 1 for i in range(len(k))]) + 1;

if len(sys.argv) > 2 + t:
	n = int(sys.argv[2 + t]);

def variable_str(i,j):
	return "x%dc%d" % (i,j);

def filename_str(k, n):
	s = "data/vdw";
	for kval in k:
		s += "-%d" % kval;
	s += "-%03d.z3" % n;
	return s;

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

	for j in range(0,t):
		d = 1;
		while i - (k[j] - 1) * d >= 0:
			monocolor_constraint = "(assert (>= %d (+" % (k[j] - 1);
			for p in range(0, k[j]):
				monocolor_constraint += " " + variable_str(i - p * d, j);
			monocolor_constraint += ")))\n";
			constraints += monocolor_constraint;
			d += 1;
 
	i += 1;
	if i < n:
		continue;

	solve_file = open(filename_str(k, i), "w");
	solve_file.write(variables + constraints);
	solve_file.close();

	z3 = Solver();
	z3.from_string(variables + constraints);

	print "vdw for t=%d, k=%s, n=%d:\n" % (t,str(k),i);
	check = z3.check();
	print "check: ", check;

	if check == sat:
		to_delete = filename_str(k, i - 1);
		if os.path.isfile(to_delete):
			os.remove(to_delete);
	else:
		unsat_file = open(filename_str(k, i), "w");
		unsat_file.write("(set-option :produce-proofs true)\n" + \
				 variables + constraints + \
				 "(check-sat)\n(get-proof)\n");
		break;
