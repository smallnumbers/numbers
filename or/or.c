#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "translation.h"

int n, t, num_edges;
int graphs_nr;
int *graph_n;
int *graph_edges;
int *graph_sets;
unsigned char **graphs;
char *edge_colors;
unsigned int ***edge_to_sets;
unsigned int **sets_per_edge_per_color;

/* number of edges in a given set that match that color */
unsigned int **edges_per_set_per_color;

int *edge_stack;
int edge_stack_n;

void print_coloring()
{
	int i;
	for (i = 0; i < num_edges; i++)
	{
		printf("%c", '0' + edge_colors[i]);
	}
	printf("\n");
}

int pop()
{
	int i;
	int edge = edge_stack[--edge_stack_n];
	int color = edge_colors[edge];

	edge_colors[edge] = -1;

	for (i = 0; i < sets_per_edge_per_color[edge][color]; i++)
	{
		unsigned int set = edge_to_sets[edge][color][i];

		edges_per_set_per_color[color][set]--;
	}
}

int push(int edge, int color)
{
	int i;
	int result = 1;

	if (edge_colors[edge] == color)
	{
		return -1;
	}

	if (edge_colors[edge] != -1)
	{
		return 0;
	}

	edge_colors[edge] = color;
	edge_stack[edge_stack_n++] = edge;

	for (i = 0; i < sets_per_edge_per_color[edge][color]; i++)
	{
		unsigned int set = edge_to_sets[edge][color][i];

		edges_per_set_per_color[color][set]++;

		if (edges_per_set_per_color[color][set] >= graph_edges[color])
		{
			result = 0;		
		}
	}

	if (!result)
	{
		pop();
	}

	return result;
}

int recursive_search(int edge)
{
	int color;

	if (edge >= num_edges)
	{
		print_coloring();
		return 1;
	}

	for (color = 0; color < t; color++)
	{
		if (push(edge, color) == 1)
		{
			int result = recursive_search(edge + 1);
			pop();

			if (result)
			{
				return result;
			}
		}
	}

	return 0;
}

int main(int argc, const char **argv)
{
	int maxK;
	int i, j, m;
	const char *input;
	int *edge_pair = (int *)malloc(2 * sizeof(int));

	if (argc < 3)
		goto usage;

	n = atoi(argv[1]);
	maxK = atoi(argv[2]);

	t = argc - 3;

	initBinomialTable(2 * n, maxK + 1);
	num_edges = nChooseK(n, 2);

	edge_colors = (char *)malloc(num_edges);
	edge_stack = (int *)malloc(num_edges * sizeof(int));
	edge_stack_n = 0;

	for (i = 0; i < num_edges; i++)
	{
		edge_colors[i] = -1;
	}

	graphs = (unsigned char **)malloc(t * sizeof(*graphs));
	graph_n = (int*)malloc(t * sizeof(*graph_n));
	graph_edges = (int*)malloc(t * sizeof(*graph_edges));
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
		graph_edges[i] = 0;
		graphs[i] = (unsigned char *)malloc(kchoose2);

		for (j = 0; j < kchoose2; j++)
		{
			if (input[j] != '0' && input[j] != '1')
			{
				fprintf(stderr, "Invalid input '%s' at position %d\n", input, j);
				goto usage;
			}

			graphs[i][j] = input[j] - '0';

			if (graphs[i][j])
			{
				graph_edges[i]++;
			}
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

		edges_per_set_per_color[i] = (unsigned int *)calloc(num_gs, sizeof(unsigned int));

		for (j = 0; j < num_gs; j++)
		{
			indexToSet(graph_n[i], j, gset);

			for (m = 0; m < g_choose_2; m++)
			{
				int e;
				if (!graphs[i][m])
				{
					continue;
				}

				indexToSet(2, m, edge_pair);

				edge_pair[0] = gset[edge_pair[0]];
				edge_pair[1] = gset[edge_pair[1]];

				e = indexOfSet(2, edge_pair);

				sets_per_edge_per_color[e][i]++;
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
				int e;
				if (!graphs[i][m])
				{
					continue;
				}

				indexToSet(2, m, edge_pair);

				edge_pair[0] = gset[edge_pair[0]];
				edge_pair[1] = gset[edge_pair[1]];

				e = indexOfSet(2, edge_pair);

				edge_to_sets[e][i][sets_per_edge_per_color[e][i]] = j;
				sets_per_edge_per_color[e][i]++;
			}
		}

		free(gset);
	}

	if (!recursive_search(0))
	{
		printf("No result\n");
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
