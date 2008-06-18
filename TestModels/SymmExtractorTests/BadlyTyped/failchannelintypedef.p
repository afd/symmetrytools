typedef T {
	 chan l = [1] of {byte};
}

proctype user() {
		T l;
		do
		:: skip
		od
		}

init {
     atomic {
	    run user();
	    run user();
	    run user();
	    }
}