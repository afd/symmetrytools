/* Variation on example on page 81 of textbook */

byte x = 2;

active proctype A()
{
   do
   :: x = 3 - x
   od
}

# define p (x == 2)
# define q (x == 1)

/*
  simplification of the never claim generated using
  spin -f '[](p || q)'
*/
never 
{    /* [](p || q) */
accept :
   if
   :: (p || q) -> goto accept
   fi
}

/*
  spin -a never.pml
  cc -o pan pan.c
  pan
*/
