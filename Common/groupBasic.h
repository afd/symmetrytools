#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#define NO_PROCS <NO_PROCS>
#define NO_CHANS <NO_CHANS>

typedef struct perm_s {
  int pr[NO_PROCS];
  int ch[NO_CHANS];
} perm_t;

/* PERMUTATION METHODS */
perm_t constructPerm(char *dcfstring);
int applyToPr(perm_t alpha, int pid);
int applyToCh(perm_t alpha, int cid);
void displayPerm(perm_t alpha);
void product(perm_t *result, perm_t alpha,perm_t beta);
bool equals(perm_t *alpha, perm_t *beta);
perm_t identityPerm();
