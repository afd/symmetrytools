active proctype user() {
		       do
		       :: skip
		       od
		       }


init {
     atomic {

	    run user();
	    run user();
	    }
}
