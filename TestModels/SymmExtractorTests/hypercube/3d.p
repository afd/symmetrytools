mtype = {packet};

chan link1 = [1] of {mtype};
chan link2 = [1] of {mtype};
chan link3 = [1] of {mtype};
chan link4 = [1] of {mtype};
chan link5 = [1] of {mtype};
chan link6 = [1] of {mtype};
chan link7 = [1] of {mtype};
chan link8 = [1] of {mtype};

pid dest = 0;

pid current = 0

inline choose_destination() {

  if
    :: _pid!=1 -> dest = 1
    :: _pid!=2 -> dest = 2
    :: _pid!=3 -> dest = 3
    :: _pid!=4 -> dest = 4
    :: _pid!=5 -> dest = 5
    :: _pid!=6 -> dest = 6
    :: _pid!=7 -> dest = 7
    :: _pid!=8 -> dest = 8
  fi
}

inline choose_next_dimension() {
   if
    :: _pid==1 && dest==2 -> if :: chosen_dimension = 0 fi
    :: _pid==1 && dest==3 -> if :: chosen_dimension = 1 fi
    :: _pid==1 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==1 && dest==5 -> if :: chosen_dimension = 2 fi
    :: _pid==1 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==1 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==1 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==1 -> if :: chosen_dimension = 0 fi
    :: _pid==2 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==2 && dest==4 -> if :: chosen_dimension = 1 fi
    :: _pid==2 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==6 -> if :: chosen_dimension = 2 fi
    :: _pid==2 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==1 -> if :: chosen_dimension = 1 fi
    :: _pid==3 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==3 && dest==4 -> if :: chosen_dimension = 0 fi
    :: _pid==3 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==7 -> if :: chosen_dimension = 2 fi
    :: _pid==3 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==4 && dest==2 -> if :: chosen_dimension = 1 fi
    :: _pid==4 && dest==3 -> if :: chosen_dimension = 0 fi
    :: _pid==4 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==8 -> if :: chosen_dimension = 2 fi
    :: _pid==5 && dest==1 -> if :: chosen_dimension = 2 fi
    :: _pid==5 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==6 -> if :: chosen_dimension = 0 fi
    :: _pid==5 && dest==7 -> if :: chosen_dimension = 1 fi
    :: _pid==5 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==6 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==2 -> if :: chosen_dimension = 2 fi
    :: _pid==6 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==5 -> if :: chosen_dimension = 0 fi
    :: _pid==6 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==6 && dest==8 -> if :: chosen_dimension = 1 fi
    :: _pid==7 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==3 -> if :: chosen_dimension = 2 fi
    :: _pid==7 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==5 -> if :: chosen_dimension = 1 fi
    :: _pid==7 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==7 && dest==8 -> if :: chosen_dimension = 0 fi
    :: _pid==8 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==4 -> if :: chosen_dimension = 2 fi
    :: _pid==8 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==8 && dest==6 -> if :: chosen_dimension = 1 fi
    :: _pid==8 && dest==7 -> if :: chosen_dimension = 0 fi
  fi;
  assert(chosen_dimension<3)
}

proctype node(chan in; chan out0; chan out1; chan out2) {
  byte chosen_dimension = 4;

loop:
  atomic { in?packet;
    current = _pid;
    if
      :: dest==_pid -> choose_destination()
      :: else -> skip
    fi
  };
  atomic {
    choose_next_dimension();
    if
    :: chosen_dimension == 0 -> out0!packet
    :: chosen_dimension == 1 -> out1!packet
    :: chosen_dimension == 2 -> out2!packet
  fi;
  chosen_dimension = 4;
    current = 0
  };
  goto loop
}

init {
  atomic {
    run node(link1,link2,link3,link5);
    run node(link2,link1,link4,link6);
    run node(link3,link4,link1,link7);
    run node(link4,link3,link2,link8);
    run node(link5,link6,link7,link1);
    run node(link6,link5,link8,link2);
    run node(link7,link8,link5,link3);
    run node(link8,link7,link6,link4);
    if
      :: link1!packet; dest = 1
      :: link2!packet; dest = 2
      :: link3!packet; dest = 3
      :: link4!packet; dest = 4
      :: link5!packet; dest = 5
      :: link6!packet; dest = 6
      :: link7!packet; dest = 7
      :: link8!packet; dest = 8
    fi
  }
}
