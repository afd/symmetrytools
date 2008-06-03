chan box1 = [1] of {pid,pid}; 
chan box2 = [1] of {pid,pid};
chan box3 = [1] of {pid,pid};
chan box4 = [1] of {pid,pid};
chan box5 = [1] of {pid,pid};
chan network = [3] of {pid,pid};
chan null = [1] of {pid,pid}

proctype mailer(chan in) {
  pid source = 0;
  pid dest = 0;
  chan out = null;

  do :: atomic
	{
	  in?source,dest;
	  if :: dest==1 -> out = box1 
	     :: dest==2 -> out = box2
	     :: dest==3 -> out = box3
	     :: dest==4 -> out = box4
	     :: dest==5 -> out = box5
	  fi
	};
	d_step { 
	  out!source,dest; out = null;
	  source = 0; dest = 0
	}
  od
}

proctype client(chan in) {
  pid source = 0, dest = 0;
  do :: d_step { in?source,dest; assert(dest==_pid); source = 0; dest = 0 }
     :: atomic
	{
	  nfull(network) ->
	  if
	    :: network!_pid,1
	    :: network!_pid,2
	    :: network!_pid,3
	    :: network!_pid,4
	    :: network!_pid,5
	  fi
	}
  od
}

init {
  atomic {
    run client(box1); run client(box2); run client(box3);
    run client(box4); run client(box5);
    run mailer(network)

  }
}
