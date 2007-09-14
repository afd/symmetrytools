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

proctype P(U myParam) {
      myParam.c[1].a[3].y = 6;
}