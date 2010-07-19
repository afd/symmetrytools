
typedef simple_struct {
		      int x;
		      };

simple_struct myArray[4];


proctype P() {

	 do ::

	     myArray[_pid].x = 100000;	 

	 if
	     :: myArray[_pid].x == 100000 ->
	    	d_step {
		       myArray[1].x = 200000;
		       myArray[2].x = 200000;
		       myArray[3].x = 200000;
}
	:: skip
	fi;

myArray[_pid].x++;

assert(myArray[_pid].x  >= 100000);

	od
}







init {
     atomic {
	    run P();
	    run P();
	    run P();
	    }
}
