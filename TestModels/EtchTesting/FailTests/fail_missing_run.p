

proctype myproc(chan x) {
  skip
		}


init {

     chan x = [1] of {chan, chan};

     myproc(x);

}




