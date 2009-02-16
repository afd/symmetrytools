

int x;

proctype P()
{
progress_with_suffix:
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
