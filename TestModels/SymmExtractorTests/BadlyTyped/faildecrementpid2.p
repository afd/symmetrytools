typedef S {
	  pid neighbour;
	  pid self;
	}

typedef T {
	  S data[3];
	}

T stuff;

proctype hello() {
			stuff.data[2].neighbour--;
			      }

init {
     atomic {
	    run hello();
	    run hello();
	    run hello();
	    run hello();
	    }
}
