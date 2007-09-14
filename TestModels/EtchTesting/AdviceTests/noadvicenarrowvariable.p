

proctype P(int x; short y; byte z) {

				   x++;
				   y = -1;
				   z = 3

				   }

init {
     run P(1000,100,1);
     }