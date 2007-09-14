mtype = { P, V };

chan s = [0] of { mtype };

bool critical[2] = false;

proctype semaphore()
{
   do
   :: s?P -> s?V -> skip
   od
}

proctype process(byte x)
{
   do
   :: s!P;
      critical[x] = true;
      /* critical section */
      assert(!critical[1 - x]);
      critical[x] = false;
      s!V
   od
}

init
{
   run semaphore();
   run process(0);
   run process (1)
}

/*
  spin -a assertion.pml
  cc -o pan pan.c
  pan
*/
