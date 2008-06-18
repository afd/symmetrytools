proctype user() {
		chan local = [1] of {byte};
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