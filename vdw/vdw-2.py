#!/usr/bin/python

import sys;
import os;

if len(sys.argv) < 3:
	print "usage: vdw-2.py k1 k2"
	exit(1);

from z3 import *;

k1 = int(sys.argv[1]);
k2 = int(sys.argv[2]);

n = k1 + k2;
if len(sys.argv) > 3:
	n = int(sys.argv[3]);

def variable_str(i):
	return "x%03d" % i;

def filename_str(k1,k2,i):
	return "data/vdw-%d-%d-%d.z3" % (k1,k2,i);

i = 0;

variables = "";
constraints = "";
while True:
	# Add variables
	variable = variable_str(i);
	variables += "(declare-const %s Int)\n" % variable;
	constraints += "(assert (>= 1 %s))\n" % variable;
	constraints += "(assert (<= 0 %s))\n" % variable;

	d = 1;
	while i - (k1 - 1) * d >= 0:
		color1_constraint = "(assert (>= %d (+" % (k1 - 1);
		for p in range(0, k1):
			color1_constraint += " " + variable_str(i - p * d);
		color1_constraint += ")))\n";
		constraints += color1_constraint;
		d += 1;
 
	d = 1;
	while i - (k2 - 1) * d >= 0:
		color2_constraint = "(assert (<= 1 (+";
		for p in range(0, k2):
			color2_constraint += " " + variable_str(i - p * d);
		color2_constraint += ")))\n";
		constraints += color2_constraint;
		d += 1;
 
	i += 1;
	if i < n:
		continue;

	solve_file = open(filename_str(k1,k2,i), "w");
	solve_file.write(variables + constraints);
	solve_file.close();

	z3 = Solver();
	z3.from_string(variables + constraints);

	print "vdw for t=2, k=(%d,%d), n=%d:" % (k1,k2,i);
	check = z3.check();
	print "check: ", check;

	if check == sat:
		to_delete = filename_str(k1, k2, i - 1);
		if os.path.isfile(to_delete):
			os.remove(to_delete);
	else:
		solve_file = open(filename_str(k1,k2,i), "w");
		solve_file.write("(set-option :produce-proofs true)\n" + \
				 variables + constraints + \
				 "(check-sat)\n(get-proof)\n");
		solve_file.close();
		break;
