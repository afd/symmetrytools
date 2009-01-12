
typedef array {
    byte aa[3]
};
array a[3];

proctype test(){
  a[1].aa[2] = 5
}

init{
  atomic{
    run test();
    run test()
  }
}
