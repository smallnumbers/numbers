#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "translation.h"

#define LENGTH 1024

int main(int argc, const char **argv)
{
	char *buffer;
	size_t len = 0;

	initBinomialTable(100, 2);

	while (getline(&buffer, &len, stdin) >= 0)
	{
		int row = 0, col;
		int l = strlen(buffer) - 1;
		int n = 2;
		
		while (n < 100 && nChooseK(n, 2) < l)
		{
			n++;
		}

		if (l != nChooseK(n, 2))
		{
			printf("error: improper length\n");
			continue;
		}

		for (row = 0; row < n; row++)
		{
			for (col = 0; col < n; col++)
			{
				if (row == col)
				{
					printf("0");
				}

				int e = indexOf(row, col);

				printf("%c", buffer[e]);
			}

			printf("\n");
		}

		printf("\n");
	}
}
