#include "group.h"

void freePerm(perm_t p) {
   free(p.pr);
   free(p.ch);
}

perm_t identityPerm() {
  return constructPerm("");
}

void displayPerm(perm_t alpha) {
  int i, j;
  printf("Processes:\n");
  for(i=0; i<NO_PROCS; i++) {
    int image = i;

    for(j=0; j<alpha.prLength; j = j+2) {
      if(alpha.pr[j]==image) {
	image = alpha.pr[j+1];
      } else if(alpha.pr[j+1]==image) {
	image = alpha.pr[j];
      }
    }
    printf("   %d -> %d\n",i,image);
  }
  
  printf("Channels:\n");  
  for(i=0; i<NO_CHANS; i++) {
    int image = i;

    for(j=0; j<alpha.chLength; j = j+2) {
      if(alpha.ch[j]==image) {
	image = alpha.ch[j+1];
      } else if(alpha.ch[j+1]==image) {
	image = alpha.ch[j];
      }
    }
    printf("   %d -> %d\n",i,image);

  }


}

perm_t constructPerm(char *transpositionsstring) {
  perm_t alpha;

  /*  int i, first = -1, current, next, number;
      char *token, temp[5];*/

  char *token;
  int prIndex;
  int chIndex;
  int noPrSwaps;
  int noChSwaps;
  int number;

  char transpositions[strlen(transpositionsstring)+1];
  
  strcpy(transpositions,transpositionsstring);

  noPrSwaps = 0;
  noChSwaps = 0;

  token = (char *)strtok(transpositions," ");
  while(token) {
    number = atoi(token);
    if(number >= NO_PROCS) {
      noChSwaps++;
    } else {
      noPrSwaps++;
    }
    strtok(NULL," ");
    token = (char *)strtok(NULL," ");
  }

  alpha.pr = (int*)malloc(2*noPrSwaps*sizeof(int));
  alpha.ch = (int*)malloc(2*noChSwaps*sizeof(int));

  alpha.prLength = 2*noPrSwaps;
  alpha.chLength = 2*noChSwaps;

  strcpy(transpositions,transpositionsstring);
  token = (char *)strtok(transpositions," ");
  prIndex = 0;
  chIndex = 0;

  while(token) {
    number = atoi(token);
    if(number >= NO_PROCS) {
      alpha.ch[chIndex++] = number-NO_PROCS;
      token = (char *)strtok(NULL," ");
      number = atoi(token);
      alpha.ch[chIndex++] = number-NO_PROCS;
    } else {
      alpha.pr[prIndex++] = number;
      token = (char *)strtok(NULL," ");
      number = atoi(token);
      alpha.pr[prIndex++] = number;
    }
    token = (char *)strtok(NULL," ");
    }

  return alpha;
}
