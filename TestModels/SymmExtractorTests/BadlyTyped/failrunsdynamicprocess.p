proctype client() {
		  
		  do
		  :: skip
		  od
		  }

proctype user() {
		run client();
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