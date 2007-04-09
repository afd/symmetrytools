#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>

#define NO_PROCS <NO_PROCS>
#define NO_CHANS <NO_CHANS>

struct perm {
  int pr[NO_PROCS];
  int ch[NO_CHANS];
};

/* PERMUTATION METHODS */
struct perm constructPerm(char *dcfstring);
int applyToPr(struct perm alpha, int pid);
int applyToCh(struct perm alpha, int cid);
void displayPerm(struct perm alpha);
void product(struct perm *result, struct perm alpha,struct perm beta);
bool equals(struct perm *alpha, struct perm *beta);
struct perm identityPerm();
