chan box1 = [1] of {pid,pid}; 
chan box2 = [1] of {pid,pid};
chan box3 = [1] of {pid,pid};
chan box4 = [1] of {pid,pid};
chan box5 = [1] of {pid,pid};
chan network = [5] of {pid,pid};
chan null = [1] of {pid,pid};

pid received_from = 255
pid just_sent = 255

proctype mailer(chan in) {
  pid source = 255;
  pid dest = 255;
  pid blocked_client = 3;
  chan out = null;
  do :: in?source,dest;
        if :: source==blocked_client -> skip
           :: else -> 
              if :: dest==1 -> out = box1 
                 :: dest==2 -> out = box2
                 :: dest==3 -> out = box3
                 :: dest==4 -> out = box4
                 :: dest==5 -> out = box5
              fi;
              out!source,dest; out = null
       fi;
       source = 255; dest = 255; out = null
  od
}

proctype client(chan in) {
  pid source = 255, dest = 255;
  do :: in?source,dest; assert(dest==_pid); received_from = source
     :: atomic { nfull(network) ->
         source = _pid;
         if :: dest = 1 :: dest = 2 :: dest = 3
            :: dest = 4 :: dest = 5
         fi;
         network!source,dest;
	 just_sent = source;	 
         source = 255; dest = 255 }
  od
}

init {
  atomic {
    run client(box1); run client(box2);
    run client(box3); run client(box4);
    run client(box5); run mailer(network)
  }
}
