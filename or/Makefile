
or: or.c
	gcc -g -lm -o or or.c translation.c

clean:
	rm -rf or

all: or

test: all
	./or 5 3 111 111
	./or 6 3 111 111
	valgrind ./or 6 4 011 111 110110
	valgrind ./or 10 4 011 111 110110

