#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

typedef unsigned long uint64_t;

uint64_t *primes;

uint64_t bsearch0(uint64_t p, uint64_t max)
{
	uint64_t min = 0;

	while (min < max) {
		uint64_t mid = min + (max - min) / 2;

		if (primes[mid] == p)
			return mid;

		if (primes[mid] < p)
			min = mid + 1;
		else
			max = mid;
	}

	return -1;
}

void sieve(uint64_t max_p)
{
	uint64_t N = (uint64_t)(max_p * sqrt((double)max_p));

	uint64_t p = 2;
	uint64_t num_p = 0;
	
	uint64_t *nums = calloc(N, sizeof(uint64_t));
	nums[0] = 1;
	nums[1] = 1;

	for (p = 2; p < N; p++) {
		uint64_t m = 2*p;
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
	const uint64_t *_a = (const uint64_t *)a;
	const uint64_t *_b = (const uint64_t *)b;

	if (*_a < *_b)
		return -1;
	if (*_a > *_b)
		return 1;
	return 0;
}

int main(int argc, const char **argv)
{
	int i, j, k;
	uint64_t *t, max_p;
	uint64_t best_k_so_far = 2;

	max_p = 1L << atoi(argv[1]);
	printf("Computing primes up to %10ld\n", max_p);

	primes = calloc(max_p, sizeof(uint64_t));
	sieve(max_p);

	for (i = 0; i < max_p; i++) {
		uint64_t best_k = 1;
		uint64_t best_d = 0;
		uint64_t d;

		for (d = 2; d < primes[i] / (best_k_so_far - 1); d += 2) {
			uint64_t p = primes[i] - d;
			k = 1;

			t = bsearch(&p, primes, i, sizeof(uint64_t), intcmp);
			while (t) {
				k++;
				if (k > best_k) {
					best_k = k;
					best_d = d;
				}

				p -= d;
				t = bsearch(&p, primes, i, sizeof(uint64_t), intcmp);
			}
		}

		if (best_k <= best_k_so_far)
			continue;
		
		best_k_so_far = best_k;

		printf("%10ld: ", primes[i]);
		for (j = best_k - 1; j >= 0; j--)
			printf("%10ld ", primes[i] - j * best_d);
		printf("\n");
	}

	return 0;
}
