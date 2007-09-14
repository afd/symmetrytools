/* Page 38 of the textbook */

proctype you_run(byte x)
{
   printf("x = %d, pid = %d\n", x, _pid)
}

init
{
   pid p0;
   pid p1;
   p0 = run you_run(0);
   p1 = run you_run(1);
   printf("pids: %d and %d\n", p0, p1)
}
