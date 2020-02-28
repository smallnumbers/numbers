#include <stdio.h>
#include <math.h>
#include <stdlib.h>
#include "translation.h"

/***********************/
/**
 * for computing binomial coefficients, we include a table, indexed first by k.
 * We also include a lookup tree for values of x where we want to find max n w/ binom(n,k) <= x.
 */
int** binomial_table = 0;
int binomial_table_maxk = 0;
int binomial_table_maxn = 0;

void initBinomialTable( int maxN, int maxK )
{
	binomial_table_maxk = maxK;
	binomial_table_maxn = maxN;
	binomial_table = (int**) malloc(sizeof(int*) * (maxK + 1));
	for ( int i = 0; i <= maxK; i++ )
	{
		binomial_table[i] = (int*) malloc(sizeof(int) * (maxN + 1));

		if ( i == 0 )
		{
			for ( int n = 0; n <= maxN; n++ )
			{
				binomial_table[0][n] = 1;
			}
		}
		else if ( i == 1 )
		{
			for ( int n = 0; n <= maxN; n++ )
			{
				/* TODO: CREATE INVERSE LOOKUP */
				binomial_table[1][n] = n;
			}
		}
		else
		{
			/* PASCAL's RULE! */
			for ( int j = 0; j < i; j++ )
			{
				binomial_table[i][j] = 0;
			}

			binomial_table[i][i] = 1;

			for ( int n = i + 1; n <= maxN; n++ )
			{
				/* TODO: CREATE INVERSE LOOKUP */
				binomial_table[i][n] = binomial_table[i][n - 1] + binomial_table[i - 1][n - 1];
			}
		}
	}
}

void cleanBinomialTable()
{
	for ( int i = 0; i <= binomial_table_maxk; i++ )
	{
		free(binomial_table[i]);
	}
	free(binomial_table);
	binomial_table = 0;
	binomial_table_maxk = 0;
	binomial_table_maxn = 0;
}

/**
 * nChooseK
 *
 * UPDATED 11/27/2012 to include a TABLE.
 */
int nChooseK( int n, int k )
{
	if ( k < 0 || n < 0 )
	{
		return 0;
	}

	if ( k == 0 || k == n )
	{
		return 1;
	}

	if ( k == 1 || k == n - 1 )
	{
		return n;
	}

	if ( k <= binomial_table_maxk && n <= binomial_table_maxn )
	{
		return binomial_table[k][n];
	}
	
	fprintf(stderr, "out-of-range: %d choose %d\n", n, k);
	exit(1);
}

/**
 * indexOf
 *
 * The co-lex index of the pair (i,j).
 */
int indexOf( int i, int j )
{
	if ( i == j )
	{
		/* bad input */
		return -1;
	}

	if ( j < i )
	{
		/* wrong order */
		return indexOf(j, i);
	}

	/* CO-LEX ORDER */

	/* THERE ARE (j choose 2) SETS WITH NUMBERS AT MOST j */
	return nChooseK(j, 2) + i;
}

/**
 * indexOfOrderedPair(i,j)
 *
 * When order matters!
 */
int indexOfOrderedPair(int i, int j)
{
	if ( i == j )
	{
		return -1;
	}

	int index = indexOf(i,j);

	if ( i < j )
	{
		return 2 * index;
	}
	else
	{
		return 2 * index + 1;
	}
}

/**
 * indexOfSet
 *
 * Get the co-lex order of the set of a given size.
 */
int indexOfSet( int size, int* set )
{
	/* ensure sortedness */
	sortSet(size, set);

	int index = 0;

	for ( int i = 0; i < size; i++ )
	{
		index += nChooseK(set[i], i + 1);
	}

	return index;
}

/**
 * indexOfSet
 *
 * Get the co-lex order of the set of a given size.
 */
int indexOfSetNoSort( int size, int* set )
{
	int index = 0;

	for ( int i = 0; i < size; i++ )
	{
		index += nChooseK(set[i], i + 1);
	}

	return index;
}

/**
 * indexToSet
 */
void indexToSet( int size, int index, int* set )
{
	for ( int i = size - 1; i >= 0; i-- )
	{
		/* find ith bit by considering largest portion of index */
		/* then lower for the next position */

		/* we need to solve for largest s with (s choose (i+1)) <= index */
		int min_elt = i;
		int max_elt = 2 * (i + 1);

		/* find the right frame */
		while ( nChooseK(max_elt, i + 1) <= index )
		{
			min_elt = max_elt;
			max_elt = max_elt << 1; /* double */
		}

		/* do binary search */
		while ( min_elt <= max_elt )
		{
			int half = (max_elt + min_elt) >> 1;

			if ( nChooseK(half, i + 1) <= index )
			{
				min_elt = half + 1;
			}
			else
			{
				max_elt = half - 1;
			}
		}

		/* place this value */
		set[i] = min_elt - 1;

		/* modify index */
		index -= nChooseK(set[i], i + 1);
	}
}

/**
 * getSuccessor
 *
 * Increment in colex-order in-place.
 *
 * @return the index for increment
 */
int getSuccessor( int size, int* set )
{
	int j = 0;
	for ( ; j < size - 1; j++ )
	{
		if ( set[j] + 1 < set[j + 1] )
		{
			set[j] = set[j] + 1;
			return j;
		}
		else
		{
			set[j] = j;
		}
	}

	/* j == size - 1 */
	set[j] = set[j] + 1;

	return j;
}

/**
 * getLexPredeccessor
 *
 * Decrement in colex-order in-place.
 *
 * @return the index for dencrement
 */
int getPredecessor( int size, int* set )
{
	int j = 0;
	for ( ; j < size; j++ )
	{
		if ( set[j] > j )
		{
			set[j] = set[j] - 1;

			for ( int i = 1; i <= j; i++ )
			{
				set[j - i] = set[j] - i;
			}

			return j;
		}
	}

	return -1;
}

/**
 * lexIndexOfSet
 *
 * Get the lex order of the set of a given size.
 */
int lexIndexOfSet( int n, int size, int* set )
{
	int index = 0;
	int prev_val = -1;
	for ( int i = 0; i < size; i++ )
	{
		for ( int l = prev_val + 1; l < set[i]; l++ )
		{
			index += nChooseK(n - (l + 1), size - (i + 1));
		}
		prev_val = set[i];
	}

	return index;
}

/**
 * lexIndexToSet
 */
void lexIndexToSet( int n, int size, int index, int* set )
{
	int t = 0;
	int m = 0;

	do
	{
		int num_sets_with_m_eq_t = nChooseK(n - 1 - t, size - m - 1);
		if ( num_sets_with_m_eq_t <= index )
		{
			index -= num_sets_with_m_eq_t;
			t++;
		}
		else
		{
			set[m] = t;
			t++;
			m++;
		}
	}
	while ( m < size );
}

/**
 * getLexSuccessor
 *
 * Increment in lex-order in-place.
 */
int getLexSuccessor( int n, int size, int* set )
{
	for ( int i = size - 1; i >= 0; i-- )
	{
		if ( set[i] < n - (size - i) )
		{
			/* INCREMENT THIS */
			set[i] = set[i] + 1;

			for ( int j = i + 1; j < size; j++ )
			{
				set[j] = set[i] + (j - i);
			}

			return i;
		}
	}

	/* WE ARE BACK AT THE BEGINNING! */
	for ( int i = 0; i < size; i++ )
	{
		set[i] = i;
	}

	return -1;
}

/**
 * getLexPredeccessor
 *
 * Decrement in lex-order in-place.
 *
 * @return the index for increment
 */
int getLexPredecessor( int n, int size, int* set )
{
	for ( int i = size - 1; i > 0; i-- )
	{
		if ( set[i] > set[i - 1] + 1 )
		{
			set[i] = set[i] - 1;
			for ( int j = i + 1; j < size; j++ )
			{
				set[j] = n - (size - j);
			}
			return i;
		}
	}

	if ( set[0] > 0 )
	{
		set[0] = set[0] - 1;
		for ( int j = 1; j < size; j++ )
		{
			set[j] = n - (size - j);
		}
		return 0;
	}

	/* WE ARE BACK AT THE END! */
	for ( int i = 0; i < size; i++ )
	{
		set[i] = n - (size - i);
	}

	return -1;
}

void testAndSwap( int* set, int i, int j )
{
	if ( i < j && set[i] > set[j] )
	{
		int temp = set[i];
		set[i] = set[j];
		set[j] = temp;
	}
}

/**
 * sortSet
 *
 * This is implemented only to size <= 5, for the case R <= 7.
 */
void sortSet( int size, int* set )
{
	if ( size <= 1 )
	{
		/* do nothing */
	}
	else if ( size == 2 )
	{
		testAndSwap(set, 0, 1);
	}
	else if ( size == 3 )
	{
		testAndSwap(set, 0, 1);
		testAndSwap(set, 0, 2);
		testAndSwap(set, 1, 2);
	}
	else if ( size == 4 )
	{
		testAndSwap(set, 0, 1);
		testAndSwap(set, 0, 2);
		testAndSwap(set, 0, 3);
		testAndSwap(set, 1, 2);
		testAndSwap(set, 1, 3);
		testAndSwap(set, 2, 3);
	}
	else if ( size == 5 )
	{
		testAndSwap(set, 0, 1);
		testAndSwap(set, 0, 2);
		testAndSwap(set, 0, 3);
		testAndSwap(set, 0, 4);
		testAndSwap(set, 1, 2);
		testAndSwap(set, 1, 3);
		testAndSwap(set, 1, 4);
		testAndSwap(set, 2, 3);
		testAndSwap(set, 2, 4);
		testAndSwap(set, 3, 4);
	}
	else if ( size == 6 )
	{

		testAndSwap(set, 0, 1);
		testAndSwap(set, 0, 2);
		testAndSwap(set, 0, 3);
		testAndSwap(set, 0, 4);
		testAndSwap(set, 0, 5);
		testAndSwap(set, 1, 2);
		testAndSwap(set, 1, 3);
		testAndSwap(set, 1, 4);
		testAndSwap(set, 1, 5);
		testAndSwap(set, 2, 3);
		testAndSwap(set, 2, 4);
		testAndSwap(set, 2, 5);
		testAndSwap(set, 3, 4);
		testAndSwap(set, 3, 5);
		testAndSwap(set, 4, 5);
	}
	else
	{
		for ( int i = 0; i < size; i++ )
		{
			int min_val = set[i];
			int min_index = i;
			for ( int j = i + 1; j < size; j++ )
			{
				if ( set[j] < min_val )
				{
					min_val = set[j];
					min_index = j;
				}
			}

			int t = set[i];
			set[i] = min_val;
			set[min_index] = t;
		}
	}
}

static inline int power(int b, int e)
{
	int p = 1;
	int i;
	for (i = 0; i < e; i++)
	{
		p *= b;
	}

	return p;
}

/**
 * indexOfTuple
 *
 * Get the product order of the set of a given size.
 */
int indexOfTuple( int n, int size, int* tuple )
{
	if ( size == 0 )
	{
		return 0;
	}
	else if ( size == 1 )
	{
		return tuple[0];
	}
	else if ( size == 2 )
	{
		return n * tuple[1] + tuple[0];
	}
	else
	{
		int base = 0;
		if ( tuple[size - 1] > 0 )
		{
			base = power(n, size - 1) * tuple[size - 1];
		}

		int offset = indexOfTuple(n, size - 1, tuple);

		return base + offset;
	}
}

/**
 * indexToTuple
 */
void indexToTuple( int n, int size, int index, int* tuple )
{
	if ( size == 0 )
	{
		return;
	}
	else if ( size == 1 )
	{
		tuple[0] = index;
	}
	else
	{
		int npow = power(n, size - 1);
		tuple[size - 1] = (int) floor(index / npow);
		int base = npow * tuple[size - 1];
		int offset = index - base;
		indexToTuple(n, size - 1, offset, tuple);
	}
}

/**
 * numSetsW
 *
 * Get the number of sets with i
 */
int numSetsW( int n, int s, int i )
{
	return nChooseK(n - 1, s - 1);
}

/**
 * numSetsWW
 *
 * Get the number of sets of size s
 * 	within [n] with BOTH entries
 */
int numSetsWW( int n, int s, int i, int j )
{
	return nChooseK(n - 2, s - 2);
}

/**
 * numSetsWWO
 *
 * Get the number of sets with first entry, but NOT second.
 */
int numSetsWWO( int n, int s, int i, int j )
{
	return nChooseK(n - 2, s - 1);
}

/**
 * numSetsWOWO
 *
 * Get the number of sets without either entry.
 */
int numSetsWOWO( int n, int s, int i, int j )
{
	return nChooseK(n - 2, s);
}

/**
 * getSetW
 */
void getSetW( int s, int i, int index, int* set )
{
	set[0] = i;

	indexToSet(s - 1, index, &(set[1]));

	for ( int k = 1; k < s; k++ )
	{
		if ( set[k] >= i )
		{
			set[k] = set[k] + 1;
		}
	}
}

/**
 * getSetWW
 */
void getSetWW( int s, int i, int j, int index, int* set )
{
	set[0] = i;
	set[1] = j;

	getSetWOWO(s - 2, i, j, index, &(set[2]));
}

/**
 * getSetWWO
 */
void getSetWWO( int s, int i, int j, int index, int* set )
{
	set[0] = i;

	getSetWOWO(s - 1, i, j, index, &(set[1]));
}

/**
 * getSetWOWO
 */
void getSetWOWO( int s, int i, int j, int index, int* set )
{
	indexToSet(s, index, set);

	if ( i > j )
	{
		int t = i;
		i = j;
		j = t;
	}

	for ( int k = 0; k < s; k++ )
	{
		if ( set[k] >= i && (k == 0 || set[k - 1] < i) )
		{
			for ( int l = k; l < s; l++ )
			{
				set[l] = set[l] + 1;
			}
		}

		if ( set[k] >= j && (k == 0 || set[k - 1] < j) )
		{
			for ( int l = k; l < s; l++ )
			{
				set[l] = set[l] + 1;
			}
		}
	}
}
