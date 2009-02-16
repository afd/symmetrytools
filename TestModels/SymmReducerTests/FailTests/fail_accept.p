
int x;

proctype P()
{
accept:
   do
:: x < 100 -> x++
od;

false;
}

init {
  atomic {
	 run P();
	 run P();
     }
}
