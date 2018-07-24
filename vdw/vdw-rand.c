#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static void print_coloring(int n, unsigned char *coloring)
{
	int i;
	for (i = 0; i < n; i++) {
		printf("%d", coloring[i]);

		if (((i + 1) % 200) == 0)
			printf("\n");
		else if (((i + 1) % 10) == 0)
			printf(" ");
	}
	printf("\n");
}

static unsigned char random_color(int t, int *k, int max_p)
{
	int p = ((unsigned)rand()) % max_p;
	int c = 0;

	while (p > k[c]) {
		p -= k[c];
		c++;
	}

	return c;
}

static int score(int t, int *k, int n, unsigned char *coloring, unsigned int *num_constraints_invalid)
{
	int c, i, j, d;
	int score = 0;

	if (num_constraints_invalid)
		memset(num_constraints_invalid, 0, n * sizeof(int));
	for (c = 0; c < t; c++) {
		int ck = k[c];

		for (i = 0; i < n; i++) {
			for (d = 1; i + d * (ck - 1) < n; d++) {
				int monochromatic = 1;

				for (j = 0; monochromatic && j < ck; j++) 
					monochromatic = (coloring[i + d * j] == c);

				if (monochromatic) {
					score += ck;
					for (j = 0; num_constraints_invalid && j < ck; j++)
						num_constraints_invalid[i + d * j]++;
				}
			}
		}
	}

	return score;
}

void randomly_color(int t, int *k, int n, int max_p, unsigned char *coloring)
{
	int i;
	for (i = 0; i < n; i++)
		coloring[i] = random_color(t, k, max_p);
}

int *scores = 0;
int *perm = 0;

int compare_scores(const void *_a, const void *_b)
{
	const int *a = (const int *)_a;
	const int *b = (const int *)_b;

	return scores[*a] - scores[*b];
}

int *num_invalid;
int vdw_iterate(int t, int *k, int n, int num_good, int degree,
		unsigned char *colorings, int max_p)
{
	int i, j, m, d;

	if (!scores) {
		scores = calloc(n, sizeof(int));
		perm = calloc(n, sizeof(int));
		num_invalid = calloc(n, sizeof(int));
	}

	for (m = 0; m < num_good; m++) {
		unsigned char *color_m = colorings + n * m;
		scores[m] = score(t, k, n, color_m, num_invalid);

		for (d = 0; d < degree; d++) {
			unsigned char *color_d = colorings + n * (num_good + degree * m + d);
			int num_swapped = 0;

			memcpy(color_d, color_m, n);
			
			for (i = 0; scores[m] && num_swapped < t && i < n; i++) {
				int p = ((unsigned)rand()) % (scores[m] + n);
				int j = 0;
				int c;

				while (p > num_invalid[j] + 1) {
					p -= num_invalid[j] + 1;
					j++;
				}

				if (!num_invalid[j])
					continue;

				c = color_d[j];
				color_d[j] = random_color(t, k, max_p);

				if (color_d[j] != c)
					num_swapped++;
			}

			scores[num_good + degree * m + d] = score(t, k, n, color_d, 0);
		}
	}

	for (i = 0; i < num_good * (degree + 1); i++)
		perm[i] = i;

	qsort(perm, n, sizeof(int), compare_scores);

	/* copy good ones into extra padding */
	for (i = 0; i < num_good; i++)
		memcpy(colorings + n * (num_good * (degree + 1) + i), colorings + n * perm[i], n);
	
	/* copy to initial seciton */
	for (i = 0; i < num_good; i++)
		memcpy(colorings + n * i, colorings + n * (num_good * (degree + 1) + i), n);

	for (i = 0; i < num_good; i++) {
		for (j = i + 1; j < num_good; j++) {
			if (!memcmp(colorings + n * i, colorings + n * j, n)) {
				randomly_color(t, k, n, max_p, colorings + n * j);
			}
		}
	}

	return scores[perm[0]];
}

/*
 * Try to prove the lower bound vdw(k1,...,kt) > n using
 * hill climing. During the iteration, keep 'num_good' best
 * solutions (measured by number of constraints failing) and
 * search from each using 'degree' perturbations.
 */
unsigned char *vdw_hill(int t, int *k, int n, int num_good, int degree)
{
	unsigned char *colorings = calloc(n * num_good * (degree + 2), 1);
	int iterations = 0;
	int iteration_summary_at = 1000;
	int i, m, c;
	int max_p = 0;

	for (c = 0; c < t; c++)
		max_p += k[c];

	for (m = 0; m < num_good; m++) {
		unsigned char *cur_coloring = colorings + m *n;

	}	

	while (vdw_iterate(t, k, n, num_good, degree, colorings, max_p)) {
		if ((++iterations % iteration_summary_at) == 0) {
			printf("best colorings after %d iterations:\n", iterations);

			for (i = 0; i < num_good; i++) {
				printf("score: %3d ", score(t, k, n, colorings + n * i, 0));
				print_coloring(n, colorings + n * i);
			}
		}
	}

	printf("complete after %d iterations, with score %d:\n", iterations, score(t, k, n, colorings, 0));
	return colorings;	
}

int main(int argc, const char **argv)
{
	int t, n, i, r, good, degree;
	int *k;
	unsigned char *result;
	struct timespec start, stop;

	if (argc < 2)
		goto usage;

	t = atoi(argv[1]);
	if (t < 2 || argc < 5 + t)
		goto usage;

	k = calloc(t, sizeof(int));

	for (i = 0; i < t; i++) {
		k[i] = atoi(argv[2 + i]);
		if (k[i] < 2)
			goto usage;
	}

	n = atoi(argv[2 + t]);
	good = atoi(argv[3 + t]);
	degree = atoi(argv[4 + t]);

	if (argc > 5 + t)
		r = atoi(argv[5 + t]);
	else
		r = (int)clock();

	
	srand(r);

	printf("vdw(%d", k[0]);
	for (i = 1; i < t; i++)
		printf(",%d", k[i]);
	printf(") ?>? %d using seed %x\n", n, r);
	fflush(stdout);

	if (clock_gettime(CLOCK_REALTIME, &start) == -1)
		printf("failed to get start time\n");

	if (result = vdw_hill(t, k, n, good, degree))
		print_coloring(n, result);	
	else
		printf("unknown\n");

	if (clock_gettime(CLOCK_REALTIME, &stop) == -1)
		printf("failed to get stop time\n");
	else if (stop.tv_sec - start.tv_sec)
		printf("finished in %ld seconds\n", stop.tv_sec - start.tv_sec);
	else
		printf("finished in %.3lf seconds\n", (stop.tv_nsec - start.tv_nsec) / 1000000000.0);

	return 0;

usage:
	printf("usage: vdw-rand <t> <k1> ... <kt> <n> <good> <degree> [rand]\n\tt > 1, ki > 1");
	return 1;
}
