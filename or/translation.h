#ifndef TRANSLATION_H_
#define TRANSLATION_H_

/**********************/

/* Now, nChooseK is calculated with a table, when initialized */
void initBinomialTable(int maxN, int maxK);
void cleanBinomialTable();

/**
 * nChooseK
 */
int nChooseK(int n, int k);

/**
 * indexOf
 *
 * The co-lex index of the pair (i,j).
 */
int indexOf(int i, int j);

/**
 * indexOfOrderedPair(i,j)
 *
 * When order matters!
 */
int indexOfOrderedPair(int i, int j);

/**
 * indexOfSet
 *
 * Get the co-lex order of the set of a given size.
 */
int indexOfSet(int size, int* set);

/**
 * indexOfSet
 *
 * Get the co-lex order of the set of a given size.
 */
int indexOfSetNoSort(int size, int* set);

/**
 * indexToSet
 */
void indexToSet(int size, int index, int* set);

/**
 * getSuccessor
 *
 * Increment in colex-order in-place.
 *
 * @return the index for increment
 */
int getSuccessor(int size, int* set);

/**
 * getLexPredeccessor
 *
 * Decrement in colex-order in-place.
 *
 * @return the index for dencrement
 */
int getPredecessor(int size, int* set);

/**
 * lexIndexOfSet
 *
 * Get the lex order of the set of a given size.
 */
int lexIndexOfSet(int n, int size, int* set);

/**
 * lexIndexToSet
 */
void lexIndexToSet(int n, int size, int index, int* set);

/**
 * getLexSuccessor
 *
 * Increment in lex-order in-place.
 *
 * @return the index for increment
 */
int getLexSuccessor(int n, int size, int* set);

/**
 * getLexPredeccessor
 *
 * Decrement in lex-order in-place.
 *
 * @return the index for dencrement
 */
int getLexPredecessor(int n, int size, int* set);

/**
 * sortSet
 */
void sortSet(int size, int* set);

/**
 * indexOfTuple
 *
 * Get the product order of the set of a given size.
 */
int indexOfTuple(int n, int size, int* tuple);

/**
 * indexToTuple
 */
void indexToTuple(int n, int size, int index, int* tuple);

/**
 * numSetsW
 *
 * Get the number of sets with i
 */
int numSetsW(int n, int s, int i);

/**
 * numSetsWW
 *
 * Get the number of sets of size s
 * 	within [n] with BOTH entries
 */
int numSetsWW(int n, int s, int i, int j);

/**
 * numSetsWWO
 *
 * Get the number of sets with first entry, but NOT second.
 */
int numSetsWWO(int n, int s, int i, int j);

/**
 * numSetsWOWO
 *
 * Get the number of sets without either entry.
 */
int numSetsWOWO(int n, int s, int i, int j);

/**
 * getSetW
 */
void getSetW(int s, int i, int index, int* set);

/**
 * getSetWW
 */
void getSetWW(int s, int i, int j, int index, int* set);

/**
 * getSetWWO
 */
void getSetWWO(int s, int i, int j, int index, int* set);

/**
 * getSetWOWO
 */
void getSetWOWO(int s, int i, int j, int index, int* set);

#endif /* TRANSLATION_H_ */
