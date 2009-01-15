
typedef array {
    byte aa[4]
};
array a[8];

proctype test(){
  a[3].aa[1] = 5
}

init{
  atomic{
    run test();
    run test()
  }
}
