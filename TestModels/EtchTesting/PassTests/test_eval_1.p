
chan A = [1] of {byte};

proctype P() {

	   bit x;
	   x = 1;


	   A?eval(x);

	   }

init {
     run P();
     }