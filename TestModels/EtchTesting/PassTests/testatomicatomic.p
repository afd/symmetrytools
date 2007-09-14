init {
     int x;

     atomic {
	    x = 4;
	    }

    atomic {
	 x--
    }
}
