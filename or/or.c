#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "translation.h"

int graphs_nr;
int *graph_n;
unsigned char **graphs;
unsigned char *edge_colors;
unsigned int ***edge_to_sets;
unsigned int **sets_per_edge_per_color;

/* number of edges in a given set that match that color */
unsigned int **edges_per_set_per_color;

int main(int argc, const char **argv)
{
	int n, num_edges;
	int maxK;
	int t, i, j, m;
	const char *input;
	int *edge_pair = (int *)malloc(2 * sizeof(int));

	if (argc < 3)
		goto usage;

	n = atoi(argv[1]);
	maxK = atoi(argv[2]);

	t = argc - 3;

	initBinomialTable(3 * n, maxK + 1);
	num_edges = nChooseK(n, 2);

	graphs = (unsigned char **)malloc(t * sizeof(*graphs));
	graph_n = (int*)malloc(t * sizeof(*graph_n));
	for (i = 0; i < t; i++)
	{
		int k, kchoose2;
		input = argv[3 + i];

		kchoose2 = strlen(input);

		k = 1;
		while (k <= maxK && nChooseK(k, 2) < kchoose2)
		{
			k++;
		}

		if (kchoose2 != nChooseK(k, 2))
		{
			fprintf(stderr, "Graph input '%s' is not a (k choose 2)\n", input);
			goto usage;
		}
		
		graph_n[i] = k;
		graphs[i] = (unsigned char *)malloc(kchoose2);

		for (j = 0; j < kchoose2; j++)
		{
			if (input[j] != '0' && input[j] != '1')
			{
				fprintf(stderr, "Invalid input '%s' at position %d\n", input, j);
				goto usage;
			}

			graphs[i][j] = input[j] - '0';
		}
	}

	/* First, count how many sets we need per edge per color */
	sets_per_edge_per_color = (unsigned int **)calloc(num_edges, sizeof(*sets_per_edge_per_color));
	for (i = 0; i < num_edges; i++)
	{
		sets_per_edge_per_color[i] = (unsigned int *)calloc(t, sizeof(int));
	}

	edges_per_set_per_color = (unsigned int **)calloc(t, sizeof(*edges_per_set_per_color));

	for (i = 0; i < t; i++)
	{
		int g_choose_2 = nChooseK(graph_n[i], 2);
		int num_gs = nChooseK(n, graph_n[i]);
		int *gset = (int *)malloc(graph_n[i] * sizeof(*gset));

		edges_per_set_per_color[i] = (unsigned int *)calloc(graph_n[i], sizeof(unsigned int));

		for (j = 0; j < num_gs; j++)
		{
			indexToSet(graph_n[i], j, gset);

			for (m = 0; m < g_choose_2; m++)
			{
				int u, v;
				if (!graphs[i][m])
				{
					continue;
				}

				indexToSet(2, m, edge_pair);

				u = gset[edge_pair[0]];
				v = gset[edge_pair[1]];

				sets_per_edge_per_color[u][i]++;
				sets_per_edge_per_color[v][i]++;
			}
		}

		free(gset);
	}

	/* Second, create lists of every set that contains each edge */
	edge_to_sets = (unsigned int ***)calloc(num_edges, sizeof(*edge_to_sets));
	for (i = 0; i < num_edges; i++)
	{
		edge_to_sets[i] = (unsigned int **)calloc(t, sizeof(unsigned int *));

		for (j = 0; j < t; j++)
		{
			edge_to_sets[i][j] = (unsigned int *)calloc(sets_per_edge_per_color[i][j], sizeof(unsigned int));
			sets_per_edge_per_color[i][j] = 0;
		}
	}

	for (i = 0; i < t; i++)
	{
		int g_choose_2 = nChooseK(graph_n[i], 2);
		int num_gs = nChooseK(n, graph_n[i]);
		int *gset = (int *)malloc(graph_n[i] * sizeof(*gset));

		for (j = 0; j < num_gs; j++)
		{
			indexToSet(graph_n[i], j, gset);

			for (m = 0; m < g_choose_2; m++)
			{
				int u, v;
				if (!graphs[i][m])
				{
					continue;
				}

				indexToSet(2, m, edge_pair);

				u = gset[edge_pair[0]];
				v = gset[edge_pair[1]];

				edge_to_sets[u][i][sets_per_edge_per_color[u][i]] = j;
				edge_to_sets[v][i][sets_per_edge_per_color[v][i]] = j;

				sets_per_edge_per_color[u][i]++;
				sets_per_edge_per_color[v][i]++;
			}
		}

		free(gset);
	}

	for (i = 0; i < t; i++)
	{
		for (j = 0; j < num_edges; j++)
		{
			free(edge_to_sets[j][i]);
		}

		free(sets_per_edge_per_color[i]);
		free(edges_per_set_per_color[i]);
		free(graphs[i]);
	}

	for (j = 0; j < num_edges; j++)
	{
		free(edge_to_sets[j]);
	}

	free(edges_per_set_per_color);
	free(edge_to_sets);
	free(graphs);
	free(graph_n);
	free(edge_pair);
	return 0;

usage:
	printf("usage: or <N> <maxK> <g1> ... <gt>\n");
	return 1;
}
