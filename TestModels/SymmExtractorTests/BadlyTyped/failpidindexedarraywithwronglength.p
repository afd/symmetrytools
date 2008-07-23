
pid A[100]

proctype P() {

	     A[_pid] = _pid;

	     }

init {
     atomic {
	    run P();
	    run P();
	    run P()
	    }
}
