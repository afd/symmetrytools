byte flag[7] = 0;
pid turn[6] = 0;
byte inCR = 0

proctype user () {
   byte k;
   bool ok;

   do :: k = 1;
         do :: k < 6 ->
               flag[_pid] = k;
               turn[k] = _pid;
again:         atomic {
                  ok = ((_pid==1)||(_pid!=1 && flag[1]<k))&&
                       ((_pid==2)||(_pid!=2 && flag[2]<k))&&
                       ((_pid==3)||(_pid!=3 && flag[3]<k))&&
                       ((_pid==4)||(_pid!=4 && flag[4]<k))&&
                       ((_pid==5)||(_pid!=5 && flag[5]<k))&&
                       ((_pid==6)||(_pid!=6 && flag[6]<k));

                  if :: ok || turn[k] != _pid
                     :: else -> goto again
                  fi
               };
               k++
            :: else -> break
         od;

         atomic { inCR++; assert(inCR == 1) };  inCR--;
         flag[_pid] = 0;
   od;
}

/* start the processes */

init {
   atomic{
      run user();
      run user();
      run user();
      run user();
      run user();
      run user();
   }
}
