
typedef S {
	  int x; byte y;
		      };

proctype P() {

	     S myArray[4];
	     
	 do ::

	     myArray[_pid].y = 100;	 

	 if
	     :: myArray[_pid].y == 100 ->
	    	d_step {
		       myArray[1].y = 200;
		       myArray[2].y = 200;
		       myArray[3].y = 200;
}
	:: skip
	fi;

myArray[_pid].y++;

assert(myArray[_pid].y  >= 100);

	od
}







init {
     atomic {
	    run P();
	    run P();
	    run P();
	    }
}
