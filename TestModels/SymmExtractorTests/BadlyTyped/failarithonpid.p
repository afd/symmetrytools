

proctype P() {
	     pid p;

	     p = _pid+1;
	     }


init {
     atomic {
	    run P();
	    run P();
	    }
}