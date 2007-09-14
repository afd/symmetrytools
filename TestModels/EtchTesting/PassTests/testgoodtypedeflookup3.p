typedef S {
	  int x;
	  chan y;
	  }

typedef T {
	S a, b[10]
	  }

typedef U {
	  T c[5];
	  S d;
	  short e;
	  }

chan ch = [6] of {byte,byte,byte,byte,byte,byte,int,int}

proctype P(U myParam) {
      myParam.c[1].a.y = ch;
}