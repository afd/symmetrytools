typedef point {
  byte x, y
}

typedef line {
  point start;
  point end[4];
  chan c = [1] of {byte};
  chan d = [1] of {byte};
  chan e = [1] of {byte,chan}
}

init {
  pid a = 4;
  byte x[10] = 5;
  byte y;
  y = 7;
  point p;
  p.x = 100;
  p.y = p.x;
  line l;
  l.start = p;
  { point b[5]
  };
  b[4]=p;
  l.end[3].y = 2;
  l.d = l.d

  
}
