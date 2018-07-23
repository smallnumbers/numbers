#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void print_coloring(int n, unsigned char *coloring)
{
	int i;
	for (i = 0; i < n; i++) {
		printf("%d", coloring[i]);

		if (((i + 1) % 50) == 0)
			printf("\n");
		else if (((i + 1) % 10) == 0)
			printf(" ");
	}
	printf("\n");
}

inline unsigned int bit(int c)
{
	return 1U << (c - 1);
}

inline unsigned int domain_remove(unsigned int *domains, int pos, int c)
{
	domains[pos] &= ~bit(c);
	return domains[pos];
}

inline int domain_allows(unsigned int *domains, int pos, int c)
{
	return domains[pos] & bit(c);
}

static void print_domains(int n, int t, unsigned int *domains)
{
	int c, i;
	for (c = 1; c <= t; c++) {
		for (i = 0; i < n; i++) {
			if (domain_allows(domains, i, c))
				printf("1");
			else
				printf("0");

			if (((i + 1) % 10) == 0)
				printf(" ");
		}
		printf("\n");
	}
}

inline void assign_color(unsigned char *coloring, unsigned int *domains,
			 int pos, int c)
{
	coloring[pos] = c;
	domains[pos] = bit(c);
}

static int domain_singleton(unsigned char *coloring, unsigned int *domains, int pos, int t)
{
	int c;

	if (coloring[pos])
		return 0;

	if (__builtin_popcount(domains[pos]) != 1)
		return 0;

	for (c = 1; c <= t; c++) {
		if (domain_allows(domains, pos, c)) {
			assign_color(coloring, domains, pos, c);
			return c;
		}
	}

	printf("BUG: we thought we were a singleton, but we didn't find the single color!\n");
	exit(1);
}

static int propagate(int t, int *k, int n, unsigned char *coloring,
		     unsigned int *domains, int pos, int c)
{
	int d, j, jstart;
	int ck = k[c - 1];

	for (jstart = 0; jstart < ck; jstart++) {
		for (d = 1; d <= n / (ck - 1); d++) {
			int monochromatic = 1;
			int last_uncolored = -1;
			int singleton_color;

			if (pos - jstart * d < 0 ||
			    pos + (ck - 1 - jstart) * d >= n)
				continue;

			for (j = 0; monochromatic && j < ck; j++) {
				int p = pos + (j - jstart) * d;

				if (!coloring[p]) {
					/* if uncolored, leave a pointer */
					if (last_uncolored < 0)
						last_uncolored = p;
					else
						monochromatic = 0;
				} else {
					monochromatic = (coloring[p] == c);
				}
			}

			if (!monochromatic)
				continue;

			/* 
			 * if everything is colored and we are monochromatic,
			 * then we have violated the coloring!
			 */
			if (last_uncolored < 0)
				return 0;

			/*
			 * if we remove the last viable color at a position,
			 * then we have violated the coloring!
			 */
			if (!domain_remove(domains, last_uncolored, c))
				return 0;

			/*
			 * if there is only one color remaining, assign that color
			 * and propagate.
			 */
			singleton_color = domain_singleton(coloring, domains, last_uncolored, t);

			if (singleton_color &&
			    !propagate(t, k, n, coloring, domains, last_uncolored, singleton_color))
				return 0;
		}
	}

	return 1;
}

static int position_to_change(int t, int *k, int n, unsigned char *coloring, unsigned int *domains)
{
	int i = 0;
	int i_to_pick = -1;
	int min_colors_available = t + 1;

	while (i < n) {
		if (coloring[i] == 0) {
			int colors_available = __builtin_popcount(domains[i]);

			if (colors_available < min_colors_available) {
				i_to_pick = i;
				min_colors_available = colors_available;
			}
		}

		i++;
	}

	return i_to_pick;
}

static unsigned char *vdw_stack(int t, int *k, int n, unsigned char *stack,
				unsigned int *domains, int h)
{
	unsigned char *next;
	unsigned int *new_domains;
	int c = 0;
	int i = 0;

	if (h > n) {
		printf("BUG: advanced in stack farther than expected!\n");
		exit(1);
	}

	next = stack + n;
	new_domains = domains + n;

	i = position_to_change(t, k, n, stack, domains);
	
	/* this is where we return a solution! */
	if (i < 0)
		return stack;

	for (c = 1; c <= t; c++) {
		unsigned char *result;
		if (!domain_allows(domains, i, c))
			continue;

		memcpy(next, stack, n);
		memcpy(new_domains, domains, n * sizeof(int));

		assign_color(next, new_domains, i, c);
		
		if (!propagate(t, k, n, next, new_domains, i, c))
			continue;

		result = vdw_stack(t, k, n, next, new_domains, h + 1);

		if (result)
			return result;
	}

	return 0;
}

static unsigned char *vdw(int t, int *k, int n)
{
	int i, c;
	int *result = NULL;
	unsigned char *stack = calloc(n * (n + 1), 1);
	unsigned int *domains = calloc(n * (n + 1), sizeof(int));
	int mask = 0;

	for (c = 1; c <= t; c++)
		mask |= bit(c);

	for (i = 0; i < n * (n + 1); i++)
		domains[i] = mask;

	return vdw_stack(t, k, n, stack, domains, 0);
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
		printf("sat:\n");
		print_coloring(n, result);	
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
