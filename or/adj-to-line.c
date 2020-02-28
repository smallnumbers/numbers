#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "translation.h"

#define LENGTH 1024

int main(int argc, const char **argv)
{
	char *buffer;
	char output[LENGTH];
	size_t len = 0;

	initBinomialTable(100, 2);

	while (getline(&buffer, &len, stdin) >= 0)
	{
		int row = 0, col;
		int n = strlen(buffer) - 1;

		for (row = 0; row < n; row++)
		{
			for (col = row + 1; col < n; col++)
			{
				int e = indexOf(row, col);

				output[e] = buffer[col];
			}

			getline(&buffer, &len, stdin);
		}

		output[nChooseK(n, 2)] = 0;
		printf("%s\n", output);
	}
}
