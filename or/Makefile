
or: or.c
	gcc -g -lm -o or or.c translation.c

clean:
	rm -rf or

all: or

test: all
	valgrind ./or 10 4 011 111 110110

