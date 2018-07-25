#!/usr/bin/python

import sys;
import os;

if len(sys.argv) < 2:
	print "usage: disc.py <C> <N>"
	exit(1);

from z3 import *;

C = int(sys.argv[1]) + 1;
N = int(sys.argv[2]);
s = sys.argv[3];

variables = "";
constraints = "";

for i in range(1, N + 1):
	variables += "(declare-const xp%d Bool)\n" % i;
	variables += "(declare-const xm%d Bool)\n" % i;
	constraints += "(assert (xor xp%d xm%d))\n" % (i,i);

for d in range(1, N / C + 1):
	i = d;
	for t in range(0, 2 * C + 1):
		variables += "(declare-const p0d%dt%d Bool)\n" % (d, t);

	# start at middle discrepancy
	constraints += "(assert p0d%dt%d)\n" % (d, C);
	for t in range(0, 2 * C + 1):
		if t != C:
			constraints += "(assert (not p0d%dt%d))\n" % (d, t);

	while i <= N:
		for t in range(0, 2 * C + 1):
			variables += "(declare-const p%dd%dt%d Bool)\n" % (i, d, t);

			if t > 0:
				constraints += "(assert (or (not (and p%dd%dt%d xp%d)) p%dd%dt%d))\n" % (i - d, d, t - 1, i, i, d, t);
			if t < 2 * C:
				constraints += "(assert (or (not (and p%dd%dt%d xm%d)) p%dd%dt%d))\n" % (i - d, d, t + 1, i, i, d, t);

			constraints += "(assert (not p%dd%dt%d))\n" % (i, d, 0);
			constraints += "(assert (not p%dd%dt%d))\n" % (i, d, 2 * C);
		i += d;

solve_file = open("data/disc-C%d-n%d.z3" % (C-1,N), "w");

if s == "unsat":
	solve_file.write("(set-option :produce-proofs true)\n");
solve_file.write(variables + constraints);

if s == "unsat":
	solve_file.write("(check-sat)\n(get-proof)\n");
else:
	solve_file.write("(check-sat)\n(get-model)\n");

solve_file.close();


