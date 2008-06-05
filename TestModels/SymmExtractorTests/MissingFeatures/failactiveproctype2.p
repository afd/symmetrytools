active [10] proctype user() {
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
