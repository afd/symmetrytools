byte noMessages = 0;

chan c0 = [1] of {pid,pid,byte};
chan c1 = [1] of {pid,pid,byte};
chan c2 = [1] of {pid,pid,byte};
chan c3 = [1] of {pid,pid,byte};
chan c4 = [1] of {pid,pid,byte};
chan c5 = [1] of {pid,pid,byte};
chan c6 = [1] of {pid,pid,byte};
chan c7 = [1] of {pid,pid,byte};
chan c8 = [1] of {pid,pid,byte};
chan c9 = [1] of {pid,pid,byte};
chan c10 = [1] of {pid,pid,byte};
chan c11 = [1] of {pid,pid,byte};
chan c12 = [1] of {pid,pid,byte};
chan c13 = [1] of {pid,pid,byte};
chan c14 = [1] of {pid,pid,byte};
chan c15 = [1] of {pid,pid,byte};

hidden byte two_to_l;
hidden byte counter

proctype node(chan in, out0, out1, out2, out3) {
  byte k; byte l; pid source; pid dest;

  do
    :: atomic {
      ((noMessages < 1) && nfull(out3)) ->
      noMessages++;
      if
	:: out3!1,_pid,1
	:: out3!2,_pid,1
	:: out3!3,_pid,1
	:: out3!4,_pid,1
	:: out3!5,_pid,1
	:: out3!6,_pid,1
	:: out3!7,_pid,1
	:: out3!8,_pid,1
	:: out3!9,_pid,1
	:: out3!10,_pid,1
	:: out3!11,_pid,1
	:: out3!12,_pid,1
	:: out3!13,_pid,1
	:: out3!14,_pid,1
	:: out3!15,_pid,1
	:: out3!16,_pid,1
      fi
    }
    :: in?source,dest,k;
       if :: d_step { dest==_pid -> dest = 0; source = 0; k = 0; noMessages-- }
	  :: d_step { else ->
		      l = 3;
		      
		      do
			:: two_to_l = 1;
			   counter = 0;
			   do
			     :: counter == l -> break
			     :: else -> two_to_l = two_to_l * 2; counter++
			   od;
			   if
			     :: (k%two_to_l)==0 -> break
			     :: else -> l--
			   fi
		      od
	  };

	     atomic {
	       if
		 :: (l == 0 && nfull(out0)) -> out0!source,dest,(k+1)
		 :: (l == 1 && nfull(out1)) -> out1!source,dest,(k+1)
		 :: (l == 2 && nfull(out2)) -> out2!source,dest,(k+1)
		 :: (l == 3 && nfull(out3)) -> out3!source,dest,(k+1)
	       fi;
	       k = 0; l = 0; source = 0; dest = 0
	     }
       fi
       
  od
  
}

init {
  atomic {
    run node(c0,c1,c2,c4,c8);
    run node(c1,c0,c3,c5,c9);
    run node(c2,c3,c0,c6,c10);
    run node(c3,c2,c1,c7,c11);
    run node(c4,c5,c6,c0,c12);
    run node(c5,c4,c7,c1,c13);
    run node(c6,c7,c4,c2,c14);
    run node(c7,c6,c5,c3,c15);
    run node(c8,c9,c10,c12,c0);
    run node(c9,c8,c11,c13,c1);
    run node(c10,c11,c8,c14,c2);
    run node(c11,c10,c9,c15,c3);
    run node(c12,c13,c14,c8,c4);
    run node(c13,c12,c15,c9,c5);
    run node(c14,c15,c12,c10,c6);
    run node(c15,c14,c13,c11,c7)
  }
}
