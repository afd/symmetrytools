proctype user() {
		chan l = [1] of {byte};
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