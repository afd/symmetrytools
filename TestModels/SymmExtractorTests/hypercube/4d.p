mtype = {packet};

chan link1 = [1] of {mtype};
chan link2 = [1] of {mtype};
chan link3 = [1] of {mtype};
chan link4 = [1] of {mtype};
chan link5 = [1] of {mtype};
chan link6 = [1] of {mtype};
chan link7 = [1] of {mtype};
chan link8 = [1] of {mtype};
chan link9 = [1] of {mtype};
chan link10 = [1] of {mtype};
chan link11 = [1] of {mtype};
chan link12 = [1] of {mtype};
chan link13 = [1] of {mtype};
chan link14 = [1] of {mtype};
chan link15 = [1] of {mtype};
chan link16 = [1] of {mtype};

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
    :: _pid!=9 -> dest = 9
    :: _pid!=10 -> dest = 10
    :: _pid!=11 -> dest = 11
    :: _pid!=12 -> dest = 12
    :: _pid!=13 -> dest = 13
    :: _pid!=14 -> dest = 14
    :: _pid!=15 -> dest = 15
    :: _pid!=16 -> dest = 16
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
    :: _pid==1 && dest==9 -> if :: chosen_dimension = 3 fi
    :: _pid==1 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==13 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==1 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==1 -> if :: chosen_dimension = 0 fi
    :: _pid==2 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==2 && dest==4 -> if :: chosen_dimension = 1 fi
    :: _pid==2 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==6 -> if :: chosen_dimension = 2 fi
    :: _pid==2 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==2 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==10 -> if :: chosen_dimension = 3 fi
    :: _pid==2 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==14 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==2 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==1 -> if :: chosen_dimension = 1 fi
    :: _pid==3 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==3 && dest==4 -> if :: chosen_dimension = 0 fi
    :: _pid==3 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==7 -> if :: chosen_dimension = 2 fi
    :: _pid==3 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==3 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==11 -> if :: chosen_dimension = 3 fi
    :: _pid==3 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==15 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==3 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==4 && dest==2 -> if :: chosen_dimension = 1 fi
    :: _pid==4 && dest==3 -> if :: chosen_dimension = 0 fi
    :: _pid==4 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==4 && dest==8 -> if :: chosen_dimension = 2 fi
    :: _pid==4 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==12 -> if :: chosen_dimension = 3 fi
    :: _pid==4 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==4 && dest==16 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==1 -> if :: chosen_dimension = 2 fi
    :: _pid==5 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==5 && dest==6 -> if :: chosen_dimension = 0 fi
    :: _pid==5 && dest==7 -> if :: chosen_dimension = 1 fi
    :: _pid==5 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==5 && dest==9 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==13 -> if :: chosen_dimension = 3 fi
    :: _pid==5 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==5 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==2 -> if :: chosen_dimension = 2 fi
    :: _pid==6 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==6 && dest==5 -> if :: chosen_dimension = 0 fi
    :: _pid==6 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==6 && dest==8 -> if :: chosen_dimension = 1 fi
    :: _pid==6 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==10 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==14 -> if :: chosen_dimension = 3 fi
    :: _pid==6 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==6 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==3 -> if :: chosen_dimension = 2 fi
    :: _pid==7 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==7 && dest==5 -> if :: chosen_dimension = 1 fi
    :: _pid==7 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==7 && dest==8 -> if :: chosen_dimension = 0 fi
    :: _pid==7 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==11 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==7 && dest==15 -> if :: chosen_dimension = 3 fi
    :: _pid==7 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==8 && dest==4 -> if :: chosen_dimension = 2 fi
    :: _pid==8 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==8 && dest==6 -> if :: chosen_dimension = 1 fi
    :: _pid==8 && dest==7 -> if :: chosen_dimension = 0 fi
    :: _pid==8 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==12 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==8 && dest==16 -> if :: chosen_dimension = 3 fi
    :: _pid==9 && dest==1 -> if :: chosen_dimension = 3 fi
    :: _pid==9 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==5 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==9 && dest==10 -> if :: chosen_dimension = 0 fi
    :: _pid==9 && dest==11 -> if :: chosen_dimension = 1 fi
    :: _pid==9 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==9 && dest==13 -> if :: chosen_dimension = 2 fi
    :: _pid==9 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==9 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==9 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==10 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==2 -> if :: chosen_dimension = 3 fi
    :: _pid==10 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==6 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==10 && dest==9 -> if :: chosen_dimension = 0 fi
    :: _pid==10 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==10 && dest==12 -> if :: chosen_dimension = 1 fi
    :: _pid==10 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==10 && dest==14 -> if :: chosen_dimension = 2 fi
    :: _pid==10 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==10 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==11 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==3 -> if :: chosen_dimension = 3 fi
    :: _pid==11 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==7 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==11 && dest==9 -> if :: chosen_dimension = 1 fi
    :: _pid==11 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==11 && dest==12 -> if :: chosen_dimension = 0 fi
    :: _pid==11 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==11 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==11 && dest==15 -> if :: chosen_dimension = 2 fi
    :: _pid==11 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==12 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==4 -> if :: chosen_dimension = 3 fi
    :: _pid==12 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==8 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==12 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==12 && dest==10 -> if :: chosen_dimension = 1 fi
    :: _pid==12 && dest==11 -> if :: chosen_dimension = 0 fi
    :: _pid==12 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==12 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==12 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==12 && dest==16 -> if :: chosen_dimension = 2 fi
    :: _pid==13 && dest==1 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==5 -> if :: chosen_dimension = 3 fi
    :: _pid==13 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==13 && dest==9 -> if :: chosen_dimension = 2 fi
    :: _pid==13 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==13 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==13 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==13 && dest==14 -> if :: chosen_dimension = 0 fi
    :: _pid==13 && dest==15 -> if :: chosen_dimension = 1 fi
    :: _pid==13 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==14 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==2 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==6 -> if :: chosen_dimension = 3 fi
    :: _pid==14 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==14 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==14 && dest==10 -> if :: chosen_dimension = 2 fi
    :: _pid==14 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==14 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==14 && dest==13 -> if :: chosen_dimension = 0 fi
    :: _pid==14 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==14 && dest==16 -> if :: chosen_dimension = 1 fi
    :: _pid==15 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==3 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==7 -> if :: chosen_dimension = 3 fi
    :: _pid==15 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==15 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==15 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==15 && dest==11 -> if :: chosen_dimension = 2 fi
    :: _pid==15 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==15 && dest==13 -> if :: chosen_dimension = 1 fi
    :: _pid==15 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==15 && dest==16 -> if :: chosen_dimension = 0 fi
    :: _pid==16 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==4 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==16 && dest==8 -> if :: chosen_dimension = 3 fi
    :: _pid==16 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==16 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==16 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==16 && dest==12 -> if :: chosen_dimension = 2 fi
    :: _pid==16 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==16 && dest==14 -> if :: chosen_dimension = 1 fi
    :: _pid==16 && dest==15 -> if :: chosen_dimension = 0 fi
  fi;
  assert(chosen_dimension<4)
}

proctype node(chan in; chan out0; chan out1; chan out2; chan out3) {
  byte chosen_dimension = 5;

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
    :: chosen_dimension == 3 -> out3!packet
  fi;
  chosen_dimension = 5;
    current = 0
  };
  goto loop
}

init {
  atomic {
    run node(link1,link2,link3,link5,link9);
    run node(link2,link1,link4,link6,link10);
    run node(link3,link4,link1,link7,link11);
    run node(link4,link3,link2,link8,link12);
    run node(link5,link6,link7,link1,link13);
    run node(link6,link5,link8,link2,link14);
    run node(link7,link8,link5,link3,link15);
    run node(link8,link7,link6,link4,link16);
    run node(link9,link10,link11,link13,link1);
    run node(link10,link9,link12,link14,link2);
    run node(link11,link12,link9,link15,link3);
    run node(link12,link11,link10,link16,link4);
    run node(link13,link14,link15,link9,link5);
    run node(link14,link13,link16,link10,link6);
    run node(link15,link16,link13,link11,link7);
    run node(link16,link15,link14,link12,link8);
    if
      :: link1!packet; dest = 1
      :: link2!packet; dest = 2
      :: link3!packet; dest = 3
      :: link4!packet; dest = 4
      :: link5!packet; dest = 5
      :: link6!packet; dest = 6
      :: link7!packet; dest = 7
      :: link8!packet; dest = 8
      :: link9!packet; dest = 9
      :: link10!packet; dest = 10
      :: link11!packet; dest = 11
      :: link12!packet; dest = 12
      :: link13!packet; dest = 13
      :: link14!packet; dest = 14
      :: link15!packet; dest = 15
      :: link16!packet; dest = 16
    fi
  }
}
