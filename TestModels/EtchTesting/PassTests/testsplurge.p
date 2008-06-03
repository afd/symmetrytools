/* Page 38 of the textbook */

active proctype splurge(int n)
{
   pid p;
   printf("%d\n", n);
   p = run splurge(n+1)
}
