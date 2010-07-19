
int myArray[4] = 100000;


proctype P() {
	 byte sum = 0;

	 do ::

	 myArray[_pid] = 100000;	 

	 if
	 :: myArray[_pid] == 100000 ->
	    	d_step {
	 	myArray[1] = 200000;
		myArray[2] = 200000;
		myArray[3] = 200000;
}
	:: skip
	fi;

        myArray[_pid]++;

	assert(myArray[_pid] >= 100000);

	od
}







init {
     atomic {
	    run P();
	    run P();
	    run P();
	    }
}
