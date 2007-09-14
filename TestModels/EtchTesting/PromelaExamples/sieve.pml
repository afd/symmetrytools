chan channel[100] = [0] of { int }

proctype first()
{
   int value = 2;
   do
   :: channel[0]!value -> value++;
   od
}

proctype last()
{
   int prime;
   channel[100]?prime;
   printf("%d\n", prime);
}

proctype sieve(byte x)
{
   int prime;
   channel[x - 1]?prime;
   printf("%d\n", prime);

   int value;
   do
   :: channel[x - 1]?value ->
      if 
      :: (value % prime == 0) ->
            skip
      :: else ->
            channel[x]!value
      fi
   od
}

init
{
   run first();
   byte x = 1;
   do
   :: (x < 100) -> run sieve(x); x++
   od;
   run last();
}
