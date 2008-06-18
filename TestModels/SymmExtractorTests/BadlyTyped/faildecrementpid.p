proctype hello(pid neighbour) {
			      neighbour--;
			      }

init {
     atomic {
	    run hello(2);
	    run hello(3);
	    run hello(4);
	    run hello(1);
	    }
}
