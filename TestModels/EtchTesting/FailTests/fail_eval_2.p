
chan A = [1] of {byte};

proctype P() {

	   A?eval(4000);

	   }

init {
     run P();
     }