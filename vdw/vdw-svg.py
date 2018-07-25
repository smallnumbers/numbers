#!/usr/bin/python

import sys;

coloring = [];

def is_number(c):
	return (c >= '0' and c <= '9');

print "<?xml version=\"1.0\" standalone=\"no\"?>"

for line in sys.stdin:
	print "<!-- %s -->" % (line[:-1]);
	if is_number(line[0]) == False:
		continue;
	
	for i in range(0, len(line)):
		if is_number(line[i]):
			coloring.append(int(line[i])-1);

colors = [ "#008000", "#800000", "#ffd42a", "#0000AA", "#9955FF" ];

max_color = max(coloring);

height=50;
width=10;

print "<svg height=\"%d\" width=\"%d\"" % (height, width * len(coloring));
print "   xmlns:svg=\"http://www.w3.org/2000/svg\"";
print "   xmlns=\"http://www.w3.org/2000/svg\">";

for i in range(len(coloring)):
	print "<rect y=\"0\" x=\"%d\" width=\"%d\" height=\"%d\"" % (width * i, width, height);
	print "      style=\"fill:%s;fill-opacity:1;stroke:#000000;stroke-width:1;stroke-opacity:1\" />" % colors[max_color - coloring[i]]; 

print "</svg>";

