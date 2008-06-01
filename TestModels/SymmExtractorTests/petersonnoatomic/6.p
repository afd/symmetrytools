byte flag[7] = 0;
pid turn[6] = 0;
byte inCR = 0

proctype P () {

  byte k;
  bool checked[7] = false;
  bool ok = false;

  do ::

     k = 1;
     do
     :: k < 3 ->
	flag[_pid] = k;
	turn[k] = _pid;

	again:
	atomic { ok = true; checked[_pid]=true };
	do
	  :: (!ok || checked[1]&&checked[2]&&checked[3]&&checked[4]&&checked[5]&&checked[6]) ->
	     atomic { do
			:: checked[1] -> checked[1] = false;
			:: checked[2] -> checked[2] = false;
			:: checked[3] -> checked[3] = false;
			:: checked[4] -> checked[4] = false;
			:: checked[5] -> checked[5] = false;
			:: checked[6] -> checked[6] = false;
			:: else -> break;
                      od;
                      break }
	  :: d_step { !checked[1] -> ok = ok && flag[1]<k; checked[1]=true }
	  :: d_step { !checked[2] -> ok = ok && flag[2]<k; checked[2]=true }
	  :: d_step { !checked[3] -> ok = ok && flag[3]<k; checked[3]=true }
	  :: d_step { !checked[4] -> ok = ok && flag[4]<k; checked[4]=true }
	  :: d_step { !checked[5] -> ok = ok && flag[5]<k; checked[5]=true }
	  :: d_step { !checked[6] -> ok = ok && flag[6]<k; checked[6]=true }

	od;
	if
	  :: atomic { ok || turn[k] != _pid -> ok = false }
	  :: atomic { else -> ok = false; goto again }
	fi;
	k++
     :: else -> break
     od;
   
     atomic { inCR++;  assert(inCR == 1) };  inCR--;
   
     flag[_pid] = 0;
  od;
}

/* initialize flags and start the processes */

init {
  atomic{
    run P();
    run P();
    run P();
    run P();
    run P();
    run P();
  }
}
