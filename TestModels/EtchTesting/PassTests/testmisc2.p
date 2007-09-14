typedef point {
  byte x, y
}

init {
  chan{byte} c, d;
  chan{byte,chan{chan{mtype,byte},bit},bool} e;
  d = e;
  byte x = 1000, y, z=10, w=false;
  a = ((3*4)==(5*(5+4)/2))||0;
  bool l;
  l = x+y
}
