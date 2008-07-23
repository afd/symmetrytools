typedef T {

	  int x;

	  }

typedef S {

	  short x;

	  }

chan A = [1] of { chan, chan };

init {

     T t;
     T s;
     
     chan B = [1] of {T};

     chan C = [1] of {S};

chan D;

chan E;

A!B,C;

A?D,E;

D!s;
E!t

     }
