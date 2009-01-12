
int a[8];

proctype test(){
  a[3] = 5
}

init{
  atomic{
    run test();
    run test()
  }
}
