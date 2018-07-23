#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int propagate(int t, int *k, int n, unsigned char *coloring)
{
	int c, i, d, j;

	for (c = 1; c <= t; c++) {
		int ck = k[c - 1];

		for (i = 0; i < n; i++) {
			for (d = 1; i + d * (ck - 1) < n; d++) {
				int monochromatic = 1;
				for (j = 0; j < ck && monochromatic; j++)
					monochromatic = (coloring[i + j * d] == c);
				if (monochromatic)
					return 0;
			}
		}
	}

	return 1;
}

static int position_to_change(int t, int *k, int n, unsigned char *coloring)
{
	int i = 0;
	while (i < n) {
		if (coloring[i] == 0)
			return i;
		i++;
	}

	return -1;
}

static unsigned char *vdw_stack(int t, int *k, int n, unsigned char *stack, int h)
{
	unsigned char *next;
	int c = 0;
	int i = 0;

	if (h > n) {
		printf("BUG: advanced in stack farther than expected!\n");
		exit(1);
	}

	next = stack + n;

	i = position_to_change(t, k, n, stack);
	if (i < 0)
		return stack;

	for (c = 1; c <= t; c++) {
		unsigned char *result;

		memcpy(next, stack, n);
		next[i] = c;
		if (!propagate(t, k, n, next))
			continue;

		if (result = vdw_stack(t, k, n, next, h + 1))
			return result;
	}

	return 0;
}

static unsigned char *vdw(int t, int *k, int n)
{
	int *result = NULL;
	unsigned char *stack = calloc(n * (n + 1), 1);

	return vdw_stack(t, k, n, stack, 0);
}

int main(int argc, const char **argv)
{
	int t, n, i;
	int *k;
	unsigned char *result;
	struct timespec start, stop;

	if (argc < 2)
		goto usage;

	t = atoi(argv[1]);
	if (t < 2 || argc < 2 + t)
		goto usage;

	k = calloc(t, sizeof(int));

	n = 0;
	for (i = 0; i < t; i++) {
		k[i] = atoi(argv[2 + i]);
		if (k[i] < 2)
			goto usage;
		n += k[i] - 1;
	}

	if (argc > 2 + t)
		n = atoi(argv[2 + t]);

	printf("vdw(%d", k[0]);
	for (i = 1; i < t; i++)
		printf(",%d", k[i]);
	printf(") ?? %d\n", n);
	fflush(stdout);

	if (clock_gettime(CLOCK_REALTIME, &start) == -1)
		printf("failed to get start time\n");

	if (result = vdw(t, k, n)) {
		printf("sat: ");
		for (i = 0; i < n; i++) {
			printf("%x", result[i]);
		}
		printf("\n");
	} else {
		printf("unsat\n");
	}

	if (clock_gettime(CLOCK_REALTIME, &stop) == -1)
		printf("failed to get stop time\n");
	else if (stop.tv_sec - start.tv_sec)
		printf("finished in %ld seconds\n", stop.tv_sec - start.tv_sec);
	else
		printf("finished in %.3lf seconds\n", (stop.tv_nsec - start.tv_nsec) / 1000000000.0);

	return 0;

usage:
	printf("usage: vdw <t> <k1> ... <kt> [n]\n\tt > 1, ki > 1");
	return 1;
}
