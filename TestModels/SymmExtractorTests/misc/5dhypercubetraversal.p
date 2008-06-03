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
chan c16 = [1] of {pid,pid,byte};
chan c17 = [1] of {pid,pid,byte};
chan c18 = [1] of {pid,pid,byte};
chan c19 = [1] of {pid,pid,byte};
chan c20 = [1] of {pid,pid,byte};
chan c21 = [1] of {pid,pid,byte};
chan c22 = [1] of {pid,pid,byte};
chan c23 = [1] of {pid,pid,byte};
chan c24 = [1] of {pid,pid,byte};
chan c25 = [1] of {pid,pid,byte};
chan c26 = [1] of {pid,pid,byte};
chan c27 = [1] of {pid,pid,byte};
chan c28 = [1] of {pid,pid,byte};
chan c29 = [1] of {pid,pid,byte};
chan c30 = [1] of {pid,pid,byte};
chan c31 = [1] of {pid,pid,byte};

hidden byte two_to_l;
hidden byte counter

proctype node(chan in, out0, out1, out2, out3, out4) {
  byte k; byte l; pid source; pid dest;

  do
    :: atomic {
      ((noMessages < 1) && nfull(out4)) ->
      noMessages++;
      if
	:: out4!1,_pid,1
	:: out4!2,_pid,1
	:: out4!3,_pid,1
	:: out4!4,_pid,1
	:: out4!5,_pid,1
	:: out4!6,_pid,1
	:: out4!7,_pid,1
	:: out4!8,_pid,1
	:: out4!9,_pid,1
	:: out4!10,_pid,1
	:: out4!11,_pid,1
	:: out4!12,_pid,1
	:: out4!13,_pid,1
	:: out4!14,_pid,1
	:: out4!15,_pid,1
	:: out4!16,_pid,1
	:: out4!17,_pid,1
	:: out4!18,_pid,1
	:: out4!19,_pid,1
	:: out4!20,_pid,1
	:: out4!21,_pid,1
	:: out4!22,_pid,1
	:: out4!23,_pid,1
	:: out4!24,_pid,1
	:: out4!25,_pid,1
	:: out4!26,_pid,1
	:: out4!27,_pid,1
	:: out4!28,_pid,1
	:: out4!29,_pid,1
	:: out4!30,_pid,1
	:: out4!31,_pid,1
	:: out4!32,_pid,1
      fi
    }
    :: in?source,dest,k;
       if :: d_step { dest==_pid -> dest = 0; source = 0; k = 0; noMessages-- }
	  ::  d_step { else ->
		      l = 4;
		      
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
		       od }
	     
	     atomic { if
	       :: (l == 0 && nfull(out0)) -> out0!source,dest,(k+1)
	       :: (l == 1 && nfull(out1)) -> out1!source,dest,(k+1)
	       :: (l == 2 && nfull(out2)) -> out2!source,dest,(k+1)
	       :: (l == 3 && nfull(out3)) -> out3!source,dest,(k+1)
	       :: (l == 4 && nfull(out4)) -> out4!source,dest,(k+1)
	     fi;
		      k = 0; l = 0; source = 0; dest = 0 }
	     
       fi
       
  od
  
}

init {
  atomic {
    run node(c0,c1,c2,c4,c8,c16);
    run node(c1,c0,c3,c5,c9,c17);
    run node(c2,c3,c0,c6,c10,c18);
    run node(c3,c2,c1,c7,c11,c19);
    run node(c4,c5,c6,c0,c12,c20);
    run node(c5,c4,c7,c1,c13,c21);
    run node(c6,c7,c4,c2,c14,c22);
    run node(c7,c6,c5,c3,c15,c23);

    run node(c8,c9,c10,c12,c0,c24);
    run node(c9,c8,c11,c13,c1,c25);
    run node(c10,c11,c8,c14,c2,c26);
    run node(c11,c10,c9,c15,c3,c27);
    run node(c12,c13,c14,c8,c4,c28);
    run node(c13,c12,c15,c9,c5,c29);
    run node(c14,c15,c12,c10,c6,c30);
    run node(c15,c14,c13,c11,c7,c31);

    run node(c16,c17,c18,c20,c24,c0);
    run node(c17,c16,c19,c21,c25,c1);
    run node(c18,c19,c16,c22,c26,c2);
    run node(c19,c18,c17,c23,c27,c3);
    run node(c20,c21,c22,c16,c28,c4);
    run node(c21,c20,c23,c17,c29,c5);
    run node(c22,c23,c20,c18,c30,c6);
    run node(c23,c22,c21,c19,c31,c7);
    run node(c24,c25,c26,c28,c16,c8);
    run node(c25,c24,c27,c29,c17,c9);
    run node(c26,c27,c24,c30,c18,c10);
    run node(c27,c26,c25,c31,c19,c11);
    run node(c28,c29,c30,c24,c20,c12);
    run node(c29,c28,c31,c25,c21,c13);
    run node(c30,c31,c28,c26,c22,c14);
    run node(c31,c30,c29,c27,c23,c15)
    
    
  }
}
