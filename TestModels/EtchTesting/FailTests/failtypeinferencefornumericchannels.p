

chan A = [1] of { chan, chan };

proctype P(chan in, out; bit myval) {

			      int temp;
			      do
					 :: in? temp; out!myval
			      od
			      }

init {

     chan B = [1] of {int};

     chan C = [1] of {short};

chan D;

chan E;

int i;

     run P(B,C,1);

A!B,C;

A?D,E;

D!5;
E!i

     }
