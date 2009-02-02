

proctype myproc(chan x) {

			x!5, x;

		}


init {

     chan x = [1] of {chan, chan};

     x ! x , x;

     run myproc(x);

}




