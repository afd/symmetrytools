#include "group.h"

bool equals(struct perm *alpha, struct perm *beta) {
  return(memcmp(alpha,beta,sizeof(struct perm))==0);
}

struct perm identityPerm() {
  return constructPerm("()");
}

struct perm constructPerm(char *dcfstring) {
  struct perm alpha;
  int i, first = -1, current, next, number;
  char *token, temp[5];

  char dcf[strlen(dcfstring)+1];
  
  strcpy(dcf,dcfstring);

  for(i=0; i<NO_PROCS; i++)
    alpha.pr[i]=i;
  for(i=0; i<NO_CHANS; i++)
    alpha.ch[i]=i;

  token = strtok(dcf,"( ");
  while(token) {

    while(token!=")") {

      if(token[strlen(token)-1]==')') { token[strlen(token)-1]='\0'; number = atoi(token); token = ")"; }
      else { number = atoi(token); token = strtok(NULL,"( "); }

      if(first==-1) { first = number; current = number; }
      else {
	next = number;
	if(current >= NO_PROCS) {

	  alpha.ch[current-NO_PROCS] = next-NO_PROCS;
	}
	else {

	  alpha.pr[current] = next;

	}
	current = next;
      }

    }

    if(first!=-1) {

      next = first;

      if(current >= NO_PROCS) {

	alpha.ch[current-NO_PROCS] = next-NO_PROCS;
      }
      else {

	  alpha.pr[current] = next;
      }
    }

    first = -1;
    token = strtok(NULL,"( ");
  }
  return alpha;
}


void displayPerm(struct perm alpha) {
  bool dealtWithProcess[NO_PROCS];
  bool dealtWithChannel[NO_CHANS];
  bool writtenBracket;
  int i, current;
  char temp[10];
  char result[100];

  result[0]='\0';
  for(i=0; i<NO_PROCS; i++) dealtWithProcess[i] = false;
  for(i=0; i<NO_CHANS; i++) dealtWithChannel[i] = false;

  for(i=0; i<NO_PROCS; i++) {

    writtenBracket = false;
    if(!dealtWithProcess[i]) {

      dealtWithProcess[i] = true;
      current = i;
      while(alpha.pr[current]!=i) {
	if(!writtenBracket) { 
	  sprintf(temp,"(%i",current);
	  strcat(result,temp);
	  writtenBracket = true; 
	}
	sprintf(temp," %i",alpha.pr[current]);
	strcat(result,temp);
	current = alpha.pr[current];
	dealtWithProcess[current] = true;
      }
      if(writtenBracket) strcat(result,")");
    }
  }

  for(i=0; i<NO_CHANS; i++) {
    writtenBracket = false;
    if(!dealtWithChannel[i]) {
      dealtWithChannel[i] = true;
      current = i;
      while(alpha.ch[current]!=i) {
	if(!writtenBracket) { sprintf(temp,"(%i",current+NO_PROCS); strcat(result,temp); writtenBracket = true; }
	sprintf(temp," %i",alpha.ch[current]+NO_PROCS);
	strcat(result,temp);
	current = alpha.ch[current];
	dealtWithChannel[current] = true;
      }
      if(writtenBracket) strcat(result,")");
    }
  }

  if(result[0]=='\0') strcat(result,"id");
  printf("%s",result);
  
}

void product(struct perm *result, struct perm alpha,struct perm beta) {
  // APPLY BETA THEN ALPHA
  int i;
  for(i=0; i<NO_PROCS; i++)
    result->pr[i]=applyToPr(alpha,applyToPr(beta,i));
  for(i=0; i<NO_CHANS; i++)
    result->ch[i]=applyToCh(alpha,applyToCh(beta,i));
}

int applyToCh(struct perm alpha,int cid) {
  return ( (cid >= 0) && (cid < NO_CHANS) ? alpha.ch[cid] : -1);
}

int applyToPr(struct perm alpha,int pid) {
  return ( (pid >= 0) && (pid < NO_PROCS) ? alpha.pr[pid] : -1);
}

