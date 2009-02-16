

proctype P()
{
false;
}

init {
  atomic {
	 run P();
	 run P();
     }
}

notrace {
      skip
      }