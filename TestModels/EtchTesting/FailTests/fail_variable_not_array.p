

proctype myproc(chan x) {

			x!x;

			x[5] = 12;


		}


init {

     chan x = [1] of {chan, chan};

     x ! x , x;

myproc(x);

}




