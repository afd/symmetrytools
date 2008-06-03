typedef point {
  byte x, y
}

init {
  chan c = [1] of {byte}, d = [2] of {byte};
  chan e = [1] of {byte,chan,bool};
  d = e;
  byte x = 1000, y, z=10, w=false;
  a = ((3*4)==(5*(5+4)/2))||0;
  bool l;
  l = x+y
}
