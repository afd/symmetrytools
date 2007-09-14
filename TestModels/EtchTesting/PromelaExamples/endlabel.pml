mtype = { P, V };

chan s = [0] of { mtype };

bool critical[2] = false;

proctype semaphore()
{
end : do
      :: s?P -> s?V -> skip
      od
}

proctype process(byte x)
{
   s!P;
   critical[x] = true;
   /* critical section */
   critical[x] = false;
   s!V
}

init
{
   run semaphore();
   run process(0);
   run process (1)
}

/*
  spin -a endlabel.pml
  cc -o pan pan.c
  pan
*/
