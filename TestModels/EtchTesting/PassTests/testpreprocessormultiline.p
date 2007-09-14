#define processortest 5+4\
-2

init {
  int x;
  x = processortest;
  assert(x==7);
}
