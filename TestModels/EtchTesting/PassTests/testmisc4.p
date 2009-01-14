
int i = 0;

proctype test(){
 i = 1
}

init{
 atomic{
   run test();
 }
} 