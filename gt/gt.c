#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

int *primes;

int bsearch0(int p, int max)
{
	int min = 0;

	while (min < max) {
		int mid = min + (max - min) / 2;

		if (primes[mid] == p)
			return mid;

		if (primes[mid] < p)
			min = mid + 1;
		else
			max = mid;
	}

	return -1;
}

void sieve(int max_p)
{
	int N = (int)(max_p * sqrt((double)max_p));

	int p = 2;
	int num_p = 0;
	
	int *nums = calloc(N, sizeof(int));
	nums[0] = 1;
	nums[1] = 1;

	for (p = 2; p < N; p++) {
		int m = 2*p;
		if (nums[p])
			continue;

		primes[num_p++] = p;

		if (num_p >= max_p)
			return;

		while (m < N) {
			nums[m] = 1;
			m += p;
		}
	}
	free(nums);
}

static int intcmp(const void *a, const void *b)
{
	return (*(const int *)a) - (*(const int *)b);
}

int main(int argc, const char **argv)
{
	int i, j, k, *t, max_p;
	int best_k_so_far = 2;

	max_p = atoi(argv[1]);

	primes = calloc(max_p, sizeof(int));
	sieve(max_p);

	for (i = 0; i < max_p; i++) {
		int best_k = 1;
		int best_d = 0;
		int d;

		for (d = 2; d < primes[i] / (best_k_so_far - 1); d += 2) {
			int p = primes[i] - d;
			k = 1;

			t = bsearch(&p, primes, i, sizeof(int), intcmp);
			while (t) {
				k++;
				if (k > best_k) {
					best_k = k;
					best_d = d;
				}

				p -= d;
				t = bsearch(&p, primes, i, sizeof(int), intcmp);
			}
		}

		if (best_k <= best_k_so_far)
			continue;
		
		best_k_so_far = best_k;

		printf("%5d: ", primes[i]);
		for (j = best_k - 1; j >= 0; j--)
			printf("%5d ", primes[i] - j * best_d);
		printf("\n");
	}

	return 0;
}
