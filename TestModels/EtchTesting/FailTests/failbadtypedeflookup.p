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

U myVar;

init {

     myVar.c[3].b.x = 20000

     }