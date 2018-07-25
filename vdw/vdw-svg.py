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

height=20;
width=20;

rows = 1;
columns = len(coloring);

while rows < columns:
	rows += 1;
	columns = (len(coloring) / rows) + 1;

rows -= 1;
columns = (len(coloring) / rows) + 1;

print "<svg height=\"%d\" width=\"%d\"" % (height * rows, width * columns);
print "   xmlns:svg=\"http://www.w3.org/2000/svg\"";
print "   xmlns=\"http://www.w3.org/2000/svg\">";

x = 0;
y = 0;

for i in range(len(coloring)):
	if x >= columns:
		x = 0;
		y += 1;

	print "<rect y=\"%d\" x=\"%d\" width=\"%d\" height=\"%d\"" % (height * y, width * x, width, height);
	print "      style=\"fill:%s;fill-opacity:1;stroke:#000000;stroke-width:1;stroke-opacity:1\" />" % colors[max_color - coloring[i]]; 
	
	x += 1;

print "</svg>";

