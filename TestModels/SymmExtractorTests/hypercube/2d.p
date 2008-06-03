mtype = {packet};

chan link1 = [1] of {mtype};
chan link2 = [1] of {mtype};
chan link3 = [1] of {mtype};
chan link4 = [1] of {mtype};

pid dest = 0;

pid current = 0

inline choose_destination() {

  if
    :: _pid!=1 -> dest = 1
    :: _pid!=2 -> dest = 2
    :: _pid!=3 -> dest = 3
    :: _pid!=4 -> dest = 4
  fi
}

inline choose_next_dimension() {
   if
    :: _pid==1 && dest==2 -> if :: chosen_dimension = 0 fi
    :: _pid==1 && dest==3 -> if :: chosen_dimension = 1 fi
    :: _pid==1 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==2 && dest==1 -> if :: chosen_dimension = 0 fi
    :: _pid==2 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==2 && dest==4 -> if :: chosen_dimension = 1 fi
    :: _pid==3 && dest==1 -> if :: chosen_dimension = 1 fi
    :: _pid==3 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==3 && dest==4 -> if :: chosen_dimension = 0 fi
    :: _pid==4 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==4 && dest==2 -> if :: chosen_dimension = 1 fi
    :: _pid==4 && dest==3 -> if :: chosen_dimension = 0 fi
  fi;
  assert(chosen_dimension<2)
}

proctype node(chan in; chan out0; chan out1) {
  byte chosen_dimension = 3;

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
  fi;
  chosen_dimension = 3;
    current = 0
  };
  goto loop
}

init {
  atomic {
    run node(link1,link2,link3);
    run node(link2,link1,link4);
    run node(link3,link4,link1);
    run node(link4,link3,link2);
    if
      :: link1!packet; dest = 1
      :: link2!packet; dest = 2
      :: link3!packet; dest = 3
      :: link4!packet; dest = 4
    fi
  }
}
