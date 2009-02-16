
int x;

proctype P()
{
accept_with_suffix:
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
