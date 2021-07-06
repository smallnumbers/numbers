#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int **sz;

static int propagate(int n, int k, unsigned char *stack, int a, int h, int size_to_beat)
{
	int i, j, jstart, d;

	if (sz[n - a][k] > 0 &&
	    h + 1 + sz[n - a][k] < size_to_beat)
		return 0;

	for (d = 1; d <= (a + 1) / (k - 1); d++) {
		int all_in = 1;

		for (j = 1; all_in && j < k; j++)
			all_in = stack[a - j * d];

		if (all_in && j == k)
			return 0;
	}

	return 1;
}

static unsigned char *compute_sz_recurse(int n, int k, unsigned char *stack,
					 unsigned char *result_space, int a, int h, int *size)
{
	int best_size = h;

	if (a >= n) {
		if (h > *size) {
			memcpy(result_space, stack, n);
			*size = h;
		}

		return result_space;
	}

	if (h >= n) {
		printf("BUG: recursion height is too large!\n");
		exit(1);
	}

	while (a < n) {
		memset(stack + a, 0, n - a);
		stack[a] = 1;

		if (propagate(n, k, stack, a, h, *size)) {
			int cur_size = *size;

			if (best_size > cur_size) {
				cur_size = best_size;
				*size = best_size;
				memcpy(result_space, stack, n);
			}

			unsigned char *result = compute_sz_recurse(n, k, stack, result_space,
								   a + 1, h + 1, &cur_size);

			if (best_size < cur_size) {
				best_size = cur_size;
				*size = cur_size;
			}
		}
		stack[a] = 0;

		a++;
	}

	return result_space;
}


static int compute_sz(int n, int k)
{
	struct timespec start, stop;
	unsigned char *stack, *result_space, *result_set;
	int i;

	stack = calloc(n, 1);
	result_space = calloc(n, 1);

	clock_gettime(CLOCK_REALTIME, &start);

	sz[n][k] = k - 1;
	result_set = compute_sz_recurse(n, k, stack, result_space, 0, 0, &sz[n][k]);

	clock_gettime(CLOCK_REALTIME, &stop);

	printf("sz(%d,%d)=%d\t", n, k, sz[n][k]);
	for (i = 0; i < n; i++)
		printf("%d", result_set[i]);
	printf("\t\t");

	if (stop.tv_sec - start.tv_sec)
		printf("finished in %ld seconds\n", stop.tv_sec - start.tv_sec);
	else
		printf("finished in %.3lf seconds\n", (stop.tv_nsec - start.tv_nsec) / 1000000000.0);

	fflush(stdout);

	return sz[n][k];
}

int main(int argc, const char **argv)
{
	int min_n, max_n, n;
	int max_k, k;
	int i;

	if (argc < 3)
		goto usage;

	min_n = atoi(argv[1]);
	max_n = atoi(argv[2]);

	max_k = max_n;
	if (argc > 3)
		max_k = atoi(argv[3]);

	sz = calloc(max_n + 1, sizeof(int *));
	for (i = 0; i <= max_n; i++)
		sz[i] = calloc(max_k + 1, sizeof(int));

	for (n = min_n; n <= max_n; n++) {
		for (k = 3; k <= max_k; k++) {
			if (k < n)
				sz[n][k] = compute_sz(n, k);
			else
				sz[n][k] = n;
		}
	}

	return 0;

usage:
	printf("usage: sz <minn> <maxn> [maxk]\n");
	return 1;
}
