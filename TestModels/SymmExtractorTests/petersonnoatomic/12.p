byte flag[13] = 0;
pid turn[6] = 0;
byte inCR = 0

proctype P () {

  byte k;
  bool checked[13] = false;
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
	  :: (!ok || checked[1]&&checked[2]&&checked[3]&&checked[4]&&checked[5]&&checked[6]&&checked[7]&&checked[8]&&checked[9]&&checked[10]&&checked[11]&&checked[12]) ->
	     atomic { do
			:: checked[1] -> checked[1] = false;
			:: checked[2] -> checked[2] = false;
			:: checked[3] -> checked[3] = false;
			:: checked[4] -> checked[4] = false;
			:: checked[5] -> checked[5] = false;
			:: checked[6] -> checked[6] = false;
			:: checked[7] -> checked[7] = false;
			:: checked[8] -> checked[8] = false;
			:: checked[9] -> checked[9] = false;
			:: checked[10] -> checked[10] = false;
			:: checked[11] -> checked[11] = false;
			:: checked[12] -> checked[12] = false;

			:: else -> break;
                      od;
                      break }
	  :: d_step { !checked[1] -> ok = ok && flag[1]<k; checked[1]=true }
	  :: d_step { !checked[2] -> ok = ok && flag[2]<k; checked[2]=true }
	  :: d_step { !checked[3] -> ok = ok && flag[3]<k; checked[3]=true }
	  :: d_step { !checked[4] -> ok = ok && flag[4]<k; checked[4]=true }
	  :: d_step { !checked[5] -> ok = ok && flag[5]<k; checked[5]=true }
	  :: d_step { !checked[6] -> ok = ok && flag[6]<k; checked[6]=true }
	  :: d_step { !checked[7] -> ok = ok && flag[7]<k; checked[7]=true }
	  :: d_step { !checked[8] -> ok = ok && flag[8]<k; checked[8]=true }
	  :: d_step { !checked[9] -> ok = ok && flag[9]<k; checked[9]=true }
	  :: d_step { !checked[10] -> ok = ok && flag[10]<k; checked[10]=true }
	  :: d_step { !checked[11] -> ok = ok && flag[11]<k; checked[11]=true }
	  :: d_step { !checked[12] -> ok = ok && flag[12]<k; checked[12]=true }

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
    run P();
    run P();
    run P();
    run P();
    run P();
    run P();
  }
}
