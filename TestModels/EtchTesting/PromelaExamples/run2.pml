/* Page 36 of the textbook */

proctype you_run(byte x)
{
   printf("x = %d, pid = %d\n", x, _pid)
}

init
{
   run you_run(0);
   run you_run(1)
}

/*
  Why does it produce the following output?

          x = 0, pid = 1
          x = 1, pid = 1
*/