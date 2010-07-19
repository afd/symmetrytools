
byte myArray[4];


proctype P() {
	 byte sum = 0;

	 do ::

	 myArray[_pid] = 2;	 

	 if
	 :: myArray[_pid] == 2 ->
	    	d_step {
	 	myArray[1] = 0;
		myArray[2] = 0;
		myArray[3] = 0;
}
	:: skip
	fi;

	assert(myArray[_pid] == 0 || myArray[_pid] == 2);

	od
}







init {
     atomic {
	    run P();
	    run P();
	    run P();
	    }
}
