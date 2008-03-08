#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#define NO_PROCS <NO_PROCS>
#define NO_CHANS <NO_CHANS>

typedef struct perm_s {
  int *pr;
  int *ch;
  int prLength;
  int chLength;
} perm_t;

/* PERMUTATION METHODS */
perm_t constructPerm(char *transpositionsstring);
void displayPerm(perm_t alpha);
perm_t identityPerm();
void freePerm(perm_t);
