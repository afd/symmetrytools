
typedef S {
	  pid x[10];
	  };

proctype P() {
	     S s;
	     pid p;

	     s.x[3]++;

	     p++;

	     }


init {
     atomic {
	    run P();
	    run P();
	    }
}