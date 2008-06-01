mtype = {request,confirmation,finished}; /* Messages used by the basic protocol */
chan link1 = [1] of {mtype};
chan link2 = [1] of {mtype};
chan link3 = [1] of {mtype};
chan link4 = [1] of {mtype};
chan link5 = [1] of {mtype};
chan link6 = [1] of {mtype};
chan link7 = [1] of {mtype};

chan nullchan = [0] of {mtype};

pid resource_user = 0;
byte priorities[9];

hidden byte priority_level

proctype client(chan link) {

  do
    /* Send a request, receive a confirmation, use the resource and send a finished message */
    :: link!request;
       atomic { link?confirmation; resource_user = _pid; assert(priorities[_pid]<7) };
       atomic { resource_user = 0; link!finished }
  od
  
}

proctype resource_allocator() {

  chan client_chan = nullchan;
  
  do
    ::
       atomic {
	 (link1?[request]||link2?[request]||link3?[request]||
	  link4?[request]||link5?[request]||link6?[request]||
	  link7?[request]);
	 
	 priority_level = 2;
	 do
	   :: priorities[1]==priority_level && link1?[request] -> client_chan = link1; break
	   :: priorities[2]==priority_level && link2?[request] -> client_chan = link2; break
	   :: priorities[3]==priority_level && link3?[request] -> client_chan = link3; break
	   :: priorities[4]==priority_level && link4?[request] -> client_chan = link4; break
	   :: priorities[5]==priority_level && link5?[request] -> client_chan = link5; break
	   :: priorities[6]==priority_level && link6?[request] -> client_chan = link6; break
	   :: priorities[7]==priority_level && link7?[request] -> client_chan = link7; break
	   :: else -> priority_level--
	 od;
	 
	 client_chan?request;
       };

       client_chan!confirmation;

       d_step { client_chan?finished; client_chan = nullchan }
       
  od
  
}

init {
  
  atomic {


    /* Run the clients and the resource allocator */
    run client(link1);
    run client(link2);
    run client(link3);
    run client(link4);
    run client(link5);
    run client(link6);
    run client(link7);

    run resource_allocator();

    
    /* Set up the priorities */
    priorities[1] = 0;
    priorities[2] = 0;
    priorities[3] = 0;
    priorities[4] = 1;
    priorities[5] = 1;
    priorities[6] = 1;
    priorities[7] = 1;
  }
  
}

