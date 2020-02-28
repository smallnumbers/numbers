
all: or adj-to-line line-to-adj

or: or.c
	gcc -g -lm -o or or.c translation.c

adj-to-line: adj-to-line.c
	gcc -g -lm -o adj-to-line adj-to-line.c translation.c

line-to-adj: line-to-adj.c
	gcc -g -lm -o line-to-adj line-to-adj.c translation.c

clean:
	rm -rf or adj-to-line line-to-adj

test: all
	./or 5 3 111 111
	./or 6 3 111 111

