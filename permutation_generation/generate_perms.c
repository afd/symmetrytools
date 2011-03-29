#include <stdio.h>
#include <assert.h>

#define MAX_PERM_SIZE 10

typedef struct perm_s
{
  unsigned int mapping[MAX_PERM_SIZE];
} perm_t;

void display(perm_t* alpha, unsigned int size)
{
  int visited[MAX_PERM_SIZE], i, j;

  int is_identity = 1;

  assert(size <= MAX_PERM_SIZE);

  for(i = 0; i < size; i++)
    {
      if(alpha->mapping[i] != i)
	{
	  is_identity = 0;
	  break;
	}
    }

  if(is_identity)
    {
      printf("id");
      return;
    }

  for(i = 0; i < MAX_PERM_SIZE; i++)
    {
      visited[i] = 0;
    }

  for(j = 0; j < size; j++)
    {
      int k, first;
      if(visited[j])
	{
	  continue;
	}

      visited[j] = 1;
      k = j;
      first = 1;
      while(alpha->mapping[k] != j)
	{
	  if(first)
	    {
	      first = 0;
	      printf("(");
	    } 
	  else
	    {
	      printf(" ");
	    }
	  printf("%d", k);
	  k = alpha->mapping[k];
	  visited[k] = 1;
	}

      if(!first)
	{
	  printf(" %d)", k);
	}

    }

}


void show_perms(unsigned int size)
{
  int i, p, offset, pos[size], dir[size], count;

  perm_t alpha;

  assert(size <= MAX_PERM_SIZE);

  count = 1;

  for(i = 0; i < size; i++)
    {
      alpha.mapping[i] = i;
    }

  printf("%d ", count++);
  display(&alpha, size);
  printf("\n");

  for(i = 0; i < size; i++)
    {
      pos[i] = 1;
      dir[i] = 1;
    }
  pos[size-1] = 0;

  i = 0;
  while(i < size-1)
    {
      for(i = offset = 0; pos[i] == size-i; i++)
	{
	  pos[i] = 1;
	  dir[i] = !dir[i];
	  if(dir[i])
	    {
	      offset++;
	    }
	}

      if(i < size-1)
	{
	  int j;

	  p = offset-1 + (dir[i] ? pos[i] : size-i-pos[i]);
	  pos[i]++;

	  for(j = 0; j < size; j++)
	    {
	      if(alpha.mapping[j] == p)
		{
		  alpha.mapping[j] = p+1;
		}
	      else if(alpha.mapping[j] == p+1)
		{
		  alpha.mapping[j] = p;
		}
	    }

	  printf("%d ", count++);
	  display(&alpha, size);
	  printf("\n");

	}

    }

}


int main(int argc, char** argv)
{
  if(2 != argc)
    {
      printf("Pass one argument, specifying number of perms to try.\n");
      return 1;
    }

  show_perms(atoi(argv[1]));

  return 0;

}
