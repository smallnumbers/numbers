#!/usr/bin/python

import sys;

if len(sys.argv) < 2:
	print "usage: sz.py <N>"
	exit(1);

from z3 import *;
import csv;
import os.path;

N = int(sys.argv[1]);

sz = {};

filename = "data/sz.csv";

if os.path.isfile(filename):
	with open(filename, "r") as csv_file:
		csv_in = csv.reader(csv_file, delimiter=' ');
		for row in csv_in:
			print row;
			n = int(row[0]);
			for i in range(1, len(row)):
				sz[(n,i+2)] = int(row[1]);

def variable_name(i):
	return "x%03d" % i;

with open(filename, "w") as csv_file:
	csv_out = csv.writer(csv_file, delimiter=' ');
	for n in range(3, N):
		k_range = range(3, min(n, 17));
		for k in k_range:	
			if (k,n) in sz:
				continue;

			z3input = "(declare-const size Int)\n";

			sizestring = "(assert (= size (+";
			for i in range(0, n):
				z3input += "(declare-const %s Int)\n" % variable_name(i);
				z3input += "(assert (< %s 2))\n" % variable_name(i);
				z3input += "(assert (>= %s 0))\n" % variable_name(i);
				sizestring += " %s" % variable_name(i);
		
			sizestring += ")))\n";
			z3input += sizestring;
	
			for i in range(0, n - k + 1):
				d = 1;
				while i + (k - 1) * d < n:
					constraint = "(assert (> %d (+" % k;
					for j in range(0, k):
						constraint += " %s" % variable_name(i + j * d);
					constraint += ")))\n";
					z3input += constraint;
					d += 1;
	
			opt_file = open("data/sz-n%03d-k%02d.z3" % (n,k), "w");
			opt_file.write(z3input);
			opt_file.close();
	
			z3 = Optimize();
			z3.from_string(z3input);
	
			size = Int('size');
			h = z3.maximize(size);
		
			c = z3.check();
			m = z3.model();
	
			sol = {};
			for x in m:
				sol[x.name()] = m[x];
	
			solstr = "";
			for i in range(n):
				solstr += str(sol[variable_name(i)]);
	
			upper = int(str(z3.upper(h)));
			sz[(n,k)] = upper;
	
			print "sz(n=%03d,k=%02d)=%s\t%s" % (n,k,upper,solstr);
			sys.stdout.flush();
	
			unsat_file = open("data/sz-n%03d-k%02d.z3" % (n, k), "w");
			unsat_file.write("(set-option :produce-proofs true)\n" + \
					 z3input + \
					 "(assert (>= size %s))\n" % (upper + 1) + \
					 "(check-sat)\n(get-proof)\n");
			unsat_file.close();

		csv_out.writerow([n] + [sz[(n,k)] for k in k_range]);
		csv_file.flush();

