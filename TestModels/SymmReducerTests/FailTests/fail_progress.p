

int x;

proctype P()
{
progress:
do
:: x > 5 -> x++
od;

false;
}

init {
  atomic {
	 run P();
	 run P();
     }
}
