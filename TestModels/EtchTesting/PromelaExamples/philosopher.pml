mtype = { pickup, putdown };

chan F[5] = [0] of { mtype };

proctype philospher(byte x)
{
   do
   :: printf("%d thinks\n", _pid);
      F[x]!pickup;
      F[(x+1)%5]!pickup;
      printf("%d eats\n", _pid);
      F[x]!putdown;
      F[(x+1)%5]!putdown;
   od
}

proctype fork(byte x)
{
   do
   :: F[x]?pickup -> F[x]?putdown
   od
}

init
{
   run philospher(0);
   run philospher(1);
   run philospher(2);
   run philospher(3);
   run philospher(4);
   run fork(0);
   run fork(1);
   run fork(2);
   run fork(3);
   run fork(4)
}
