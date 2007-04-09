#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#define NO_PROCS <NO_PROCS>
#define NO_CHANS <NO_CHANS>

struct perm {
  int *pr;
  int *ch;
  int prLength;
  int chLength;
};

/* PERMUTATION METHODS */
struct perm constructPerm(char *transpositionsstring);
void displayPerm(struct perm alpha);
struct perm identityPerm();
