
chan A = [1] of {byte};

proctype P() {

	   int x;

	   A?eval(x);

	   }

init {
     run P();
     }