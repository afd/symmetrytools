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
chan link17 = [1] of {mtype};
chan link18 = [1] of {mtype};
chan link19 = [1] of {mtype};
chan link20 = [1] of {mtype};
chan link21 = [1] of {mtype};
chan link22 = [1] of {mtype};
chan link23 = [1] of {mtype};
chan link24 = [1] of {mtype};
chan link25 = [1] of {mtype};
chan link26 = [1] of {mtype};
chan link27 = [1] of {mtype};
chan link28 = [1] of {mtype};
chan link29 = [1] of {mtype};
chan link30 = [1] of {mtype};
chan link31 = [1] of {mtype};
chan link32 = [1] of {mtype};

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
    :: _pid!=17 -> dest = 17
    :: _pid!=18 -> dest = 18
    :: _pid!=19 -> dest = 19
    :: _pid!=20 -> dest = 20
    :: _pid!=21 -> dest = 21
    :: _pid!=22 -> dest = 22
    :: _pid!=23 -> dest = 23
    :: _pid!=24 -> dest = 24
    :: _pid!=25 -> dest = 25
    :: _pid!=26 -> dest = 26
    :: _pid!=27 -> dest = 27
    :: _pid!=28 -> dest = 28
    :: _pid!=29 -> dest = 29
    :: _pid!=30 -> dest = 30
    :: _pid!=31 -> dest = 31
    :: _pid!=32 -> dest = 32
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
    :: _pid==1 && dest==17 -> if :: chosen_dimension = 4 fi
    :: _pid==1 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==21 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==25 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==29 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==1 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==2 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==18 -> if :: chosen_dimension = 4 fi
    :: _pid==2 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==22 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==26 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==30 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==2 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==3 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==19 -> if :: chosen_dimension = 4 fi
    :: _pid==3 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==23 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==27 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==31 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==3 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==4 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==20 -> if :: chosen_dimension = 4 fi
    :: _pid==4 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==24 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==28 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==4 && dest==32 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==5 && dest==17 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==21 -> if :: chosen_dimension = 4 fi
    :: _pid==5 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==25 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==29 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==5 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==6 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==18 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==22 -> if :: chosen_dimension = 4 fi
    :: _pid==6 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==26 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==30 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==6 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==7 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==19 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==23 -> if :: chosen_dimension = 4 fi
    :: _pid==7 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==27 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==31 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==7 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==8 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==20 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==24 -> if :: chosen_dimension = 4 fi
    :: _pid==8 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==28 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==8 && dest==32 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
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
    :: _pid==9 && dest==17 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==21 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==25 -> if :: chosen_dimension = 4 fi
    :: _pid==9 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==29 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==9 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
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
    :: _pid==10 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==18 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==22 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==26 -> if :: chosen_dimension = 4 fi
    :: _pid==10 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==30 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==10 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
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
    :: _pid==11 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==19 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==23 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==27 -> if :: chosen_dimension = 4 fi
    :: _pid==11 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==31 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==11 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
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
    :: _pid==12 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==20 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==24 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==28 -> if :: chosen_dimension = 4 fi
    :: _pid==12 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==12 && dest==32 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
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
    :: _pid==13 && dest==17 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==21 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==25 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==29 -> if :: chosen_dimension = 4 fi
    :: _pid==13 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==13 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
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
    :: _pid==14 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==18 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==22 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==26 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==30 -> if :: chosen_dimension = 4 fi
    :: _pid==14 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==14 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
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
    :: _pid==15 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==19 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==23 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==27 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==15 && dest==31 -> if :: chosen_dimension = 4 fi
    :: _pid==15 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
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
    :: _pid==16 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==20 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==24 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==28 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==16 && dest==32 -> if :: chosen_dimension = 4 fi
    :: _pid==17 && dest==1 -> if :: chosen_dimension = 4 fi
    :: _pid==17 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==5 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==9 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==13 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==17 && dest==18 -> if :: chosen_dimension = 0 fi
    :: _pid==17 && dest==19 -> if :: chosen_dimension = 1 fi
    :: _pid==17 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==17 && dest==21 -> if :: chosen_dimension = 2 fi
    :: _pid==17 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==17 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==17 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==17 && dest==25 -> if :: chosen_dimension = 3 fi
    :: _pid==17 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==29 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==17 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==2 -> if :: chosen_dimension = 4 fi
    :: _pid==18 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==6 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==10 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==14 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==18 && dest==17 -> if :: chosen_dimension = 0 fi
    :: _pid==18 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==18 && dest==20 -> if :: chosen_dimension = 1 fi
    :: _pid==18 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==18 && dest==22 -> if :: chosen_dimension = 2 fi
    :: _pid==18 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==18 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==18 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==26 -> if :: chosen_dimension = 3 fi
    :: _pid==18 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==30 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==18 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==3 -> if :: chosen_dimension = 4 fi
    :: _pid==19 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==7 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==11 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==15 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==19 && dest==17 -> if :: chosen_dimension = 1 fi
    :: _pid==19 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==19 && dest==20 -> if :: chosen_dimension = 0 fi
    :: _pid==19 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==19 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==19 && dest==23 -> if :: chosen_dimension = 2 fi
    :: _pid==19 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==19 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==27 -> if :: chosen_dimension = 3 fi
    :: _pid==19 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==31 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==19 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==4 -> if :: chosen_dimension = 4 fi
    :: _pid==20 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==8 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==12 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==16 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==20 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==20 && dest==18 -> if :: chosen_dimension = 1 fi
    :: _pid==20 && dest==19 -> if :: chosen_dimension = 0 fi
    :: _pid==20 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==20 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==20 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==20 && dest==24 -> if :: chosen_dimension = 2 fi
    :: _pid==20 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==28 -> if :: chosen_dimension = 3 fi
    :: _pid==20 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==20 && dest==32 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==1 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==5 -> if :: chosen_dimension = 4 fi
    :: _pid==21 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==9 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==13 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==21 && dest==17 -> if :: chosen_dimension = 2 fi
    :: _pid==21 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==21 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==21 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==21 && dest==22 -> if :: chosen_dimension = 0 fi
    :: _pid==21 && dest==23 -> if :: chosen_dimension = 1 fi
    :: _pid==21 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==21 && dest==25 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==29 -> if :: chosen_dimension = 3 fi
    :: _pid==21 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==21 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==2 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==6 -> if :: chosen_dimension = 4 fi
    :: _pid==22 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==10 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==14 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==22 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==22 && dest==18 -> if :: chosen_dimension = 2 fi
    :: _pid==22 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==22 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==22 && dest==21 -> if :: chosen_dimension = 0 fi
    :: _pid==22 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==22 && dest==24 -> if :: chosen_dimension = 1 fi
    :: _pid==22 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==26 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==30 -> if :: chosen_dimension = 3 fi
    :: _pid==22 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==22 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==3 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==7 -> if :: chosen_dimension = 4 fi
    :: _pid==23 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==11 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==15 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==23 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==23 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==23 && dest==19 -> if :: chosen_dimension = 2 fi
    :: _pid==23 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==23 && dest==21 -> if :: chosen_dimension = 1 fi
    :: _pid==23 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==23 && dest==24 -> if :: chosen_dimension = 0 fi
    :: _pid==23 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==27 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==23 && dest==31 -> if :: chosen_dimension = 3 fi
    :: _pid==23 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==4 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==8 -> if :: chosen_dimension = 4 fi
    :: _pid==24 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==12 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==16 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==24 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==24 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==24 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==24 && dest==20 -> if :: chosen_dimension = 2 fi
    :: _pid==24 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==24 && dest==22 -> if :: chosen_dimension = 1 fi
    :: _pid==24 && dest==23 -> if :: chosen_dimension = 0 fi
    :: _pid==24 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==28 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==24 && dest==32 -> if :: chosen_dimension = 3 fi
    :: _pid==25 && dest==1 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==5 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==9 -> if :: chosen_dimension = 4 fi
    :: _pid==25 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==13 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==25 && dest==17 -> if :: chosen_dimension = 3 fi
    :: _pid==25 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==21 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==25 && dest==26 -> if :: chosen_dimension = 0 fi
    :: _pid==25 && dest==27 -> if :: chosen_dimension = 1 fi
    :: _pid==25 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==25 && dest==29 -> if :: chosen_dimension = 2 fi
    :: _pid==25 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==25 && dest==31 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==25 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==26 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==2 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==6 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==10 -> if :: chosen_dimension = 4 fi
    :: _pid==26 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==14 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==26 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==18 -> if :: chosen_dimension = 3 fi
    :: _pid==26 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==22 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==26 && dest==25 -> if :: chosen_dimension = 0 fi
    :: _pid==26 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==26 && dest==28 -> if :: chosen_dimension = 1 fi
    :: _pid==26 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==26 && dest==30 -> if :: chosen_dimension = 2 fi
    :: _pid==26 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==26 && dest==32 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==27 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==3 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==7 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==11 -> if :: chosen_dimension = 4 fi
    :: _pid==27 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==15 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==27 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==19 -> if :: chosen_dimension = 3 fi
    :: _pid==27 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==23 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==27 && dest==25 -> if :: chosen_dimension = 1 fi
    :: _pid==27 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==27 && dest==28 -> if :: chosen_dimension = 0 fi
    :: _pid==27 && dest==29 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==27 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==27 && dest==31 -> if :: chosen_dimension = 2 fi
    :: _pid==27 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==28 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==4 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==8 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==12 -> if :: chosen_dimension = 4 fi
    :: _pid==28 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==16 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==28 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==20 -> if :: chosen_dimension = 3 fi
    :: _pid==28 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==24 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==28 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==28 && dest==26 -> if :: chosen_dimension = 1 fi
    :: _pid==28 && dest==27 -> if :: chosen_dimension = 0 fi
    :: _pid==28 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==28 && dest==30 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==28 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==28 && dest==32 -> if :: chosen_dimension = 2 fi
    :: _pid==29 && dest==1 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==3 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==5 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==7 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==9 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==11 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==13 -> if :: chosen_dimension = 4 fi
    :: _pid==29 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==15 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==29 && dest==17 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==19 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==21 -> if :: chosen_dimension = 3 fi
    :: _pid==29 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==23 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==29 && dest==25 -> if :: chosen_dimension = 2 fi
    :: _pid==29 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==29 && dest==27 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==29 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==29 && dest==30 -> if :: chosen_dimension = 0 fi
    :: _pid==29 && dest==31 -> if :: chosen_dimension = 1 fi
    :: _pid==29 && dest==32 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==30 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==2 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==4 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==6 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==8 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==10 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==12 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==14 -> if :: chosen_dimension = 4 fi
    :: _pid==30 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==16 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==30 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==18 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==20 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==22 -> if :: chosen_dimension = 3 fi
    :: _pid==30 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==24 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==30 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==30 && dest==26 -> if :: chosen_dimension = 2 fi
    :: _pid==30 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==30 && dest==28 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==30 && dest==29 -> if :: chosen_dimension = 0 fi
    :: _pid==30 && dest==31 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==30 && dest==32 -> if :: chosen_dimension = 1 fi
    :: _pid==31 && dest==1 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==2 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==3 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==4 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==5 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==6 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==7 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==8 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==9 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==10 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==11 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==12 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==13 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==14 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==15 -> if :: chosen_dimension = 4 fi
    :: _pid==31 && dest==16 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==31 && dest==17 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==18 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==19 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==20 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==21 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==22 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==23 -> if :: chosen_dimension = 3 fi
    :: _pid==31 && dest==24 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==31 && dest==25 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==31 && dest==26 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==31 && dest==27 -> if :: chosen_dimension = 2 fi
    :: _pid==31 && dest==28 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==31 && dest==29 -> if :: chosen_dimension = 1 fi
    :: _pid==31 && dest==30 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==31 && dest==32 -> if :: chosen_dimension = 0 fi
    :: _pid==32 && dest==1 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==2 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==3 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==4 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==5 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==6 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==7 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==8 -> if :: chosen_dimension = 3 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==9 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==10 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==11 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==12 -> if :: chosen_dimension = 2 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==13 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==14 -> if :: chosen_dimension = 1 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==15 -> if :: chosen_dimension = 0 :: chosen_dimension = 4 fi
    :: _pid==32 && dest==16 -> if :: chosen_dimension = 4 fi
    :: _pid==32 && dest==17 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==18 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==19 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==20 -> if :: chosen_dimension = 2 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==21 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==22 -> if :: chosen_dimension = 1 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==23 -> if :: chosen_dimension = 0 :: chosen_dimension = 3 fi
    :: _pid==32 && dest==24 -> if :: chosen_dimension = 3 fi
    :: _pid==32 && dest==25 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==32 && dest==26 -> if :: chosen_dimension = 1 :: chosen_dimension = 2 fi
    :: _pid==32 && dest==27 -> if :: chosen_dimension = 0 :: chosen_dimension = 2 fi
    :: _pid==32 && dest==28 -> if :: chosen_dimension = 2 fi
    :: _pid==32 && dest==29 -> if :: chosen_dimension = 0 :: chosen_dimension = 1 fi
    :: _pid==32 && dest==30 -> if :: chosen_dimension = 1 fi
    :: _pid==32 && dest==31 -> if :: chosen_dimension = 0 fi
  fi;
  assert(chosen_dimension<5)
}

proctype node(chan in; chan out0; chan out1; chan out2; chan out3; chan out4) {
  byte chosen_dimension = 6;

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
    :: chosen_dimension == 4 -> out4!packet
  fi;
  chosen_dimension = 6;
    current = 0
  };
  goto loop
}

init {
  atomic {
    run node(link1,link2,link3,link5,link9,link17);
    run node(link2,link1,link4,link6,link10,link18);
    run node(link3,link4,link1,link7,link11,link19);
    run node(link4,link3,link2,link8,link12,link20);
    run node(link5,link6,link7,link1,link13,link21);
    run node(link6,link5,link8,link2,link14,link22);
    run node(link7,link8,link5,link3,link15,link23);
    run node(link8,link7,link6,link4,link16,link24);
    run node(link9,link10,link11,link13,link1,link25);
    run node(link10,link9,link12,link14,link2,link26);
    run node(link11,link12,link9,link15,link3,link27);
    run node(link12,link11,link10,link16,link4,link28);
    run node(link13,link14,link15,link9,link5,link29);
    run node(link14,link13,link16,link10,link6,link30);
    run node(link15,link16,link13,link11,link7,link31);
    run node(link16,link15,link14,link12,link8,link32);
    run node(link17,link18,link19,link21,link25,link1);
    run node(link18,link17,link20,link22,link26,link2);
    run node(link19,link20,link17,link23,link27,link3);
    run node(link20,link19,link18,link24,link28,link4);
    run node(link21,link22,link23,link17,link29,link5);
    run node(link22,link21,link24,link18,link30,link6);
    run node(link23,link24,link21,link19,link31,link7);
    run node(link24,link23,link22,link20,link32,link8);
    run node(link25,link26,link27,link29,link17,link9);
    run node(link26,link25,link28,link30,link18,link10);
    run node(link27,link28,link25,link31,link19,link11);
    run node(link28,link27,link26,link32,link20,link12);
    run node(link29,link30,link31,link25,link21,link13);
    run node(link30,link29,link32,link26,link22,link14);
    run node(link31,link32,link29,link27,link23,link15);
    run node(link32,link31,link30,link28,link24,link16);
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
      :: link17!packet; dest = 17
      :: link18!packet; dest = 18
      :: link19!packet; dest = 19
      :: link20!packet; dest = 20
      :: link21!packet; dest = 21
      :: link22!packet; dest = 22
      :: link23!packet; dest = 23
      :: link24!packet; dest = 24
      :: link25!packet; dest = 25
      :: link26!packet; dest = 26
      :: link27!packet; dest = 27
      :: link28!packet; dest = 28
      :: link29!packet; dest = 29
      :: link30!packet; dest = 30
      :: link31!packet; dest = 31
      :: link32!packet; dest = 32
    fi
  }
}
