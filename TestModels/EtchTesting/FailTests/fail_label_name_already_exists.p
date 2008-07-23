
bool flag;


typedef finish {
	       int a, b;
	       }

proctype P() {
	     skip;
	     if
	     :: flag -> skip
	     :: else -> skip
	     fi;
finish:
	     flag = false
	     }


mtype = { x, y, z };


init {

     run P();

     
     }