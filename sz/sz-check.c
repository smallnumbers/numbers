#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

int main(int argc, const char **argv)
{
	int k;
	int i, j, n, p;
	const char *set;

	if (argc < 3)
		goto usage;

	k = atoi(argv[1]);
	set = argv[2];
	n = strlen(set);

	for (i = 0; i < n; i++) {
		if (set[i] == '0')
			continue;

		for (j = 1; i + (k - 1) * j < n; j++) {
			int all_in = 1;

			for (p = 1; all_in && p < k; p++) {
				all_in = (set[i + p * j] == '1');
			}

			if (all_in) {
				printf("AP at i: %d, j: %d\n", i, j);
				return 1;
			}
		}
	}

	return 0;

usage:
	printf("usage: sz-check <k> <set>\n");
	return 1;
}
