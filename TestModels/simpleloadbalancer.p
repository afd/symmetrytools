chan clients[6] = [1] of {byte};
chan servers[3] = [1] of {chan};
chan loadbalancers[2] = [1] of {chan};
chan null = [1] of {byte}

proctype client(chan in; chan out) {
  do
    :: out!in
    :: in?0
  od
}

proctype server(chan in) {
  chan callback = null;
  do
    :: atomic {
      in?callback;
      callback!0;
      callback = null
    }
  od
}

proctype loadbalancer(chan in, out1, out2, out3) {
  chan clientchan = null;
  do
    :: atomic {
      in?clientchan;
      if
	:: len(out1)<=len(out2)&&len(out1)<=len(out3)&&nfull(out1) ->
	   out1!clientchan
	:: len(out2)<=len(out3)&&len(out2)<=len(out1)&&nfull(out2) ->
	   out2!clientchan
	:: len(out3)<=len(out1)&&len(out3)<=len(out2)&&nfull(out3) ->
	   out3!clientchan
      fi;
      clientchan = null
    }
  od  
}

init {
  atomic {
    run client(clients[0],loadbalancers);
    run client(clients[1],loadbalancers[0]);
    run client(clients[2],loadbalancers[0]);
    run client(clients[3],loadbalancers[1]);
    run client(clients[4],loadbalancers[1]);
    run client(clients[5],loadbalancers[1]);
    
    run server(servers[0]);
    run server(servers[1]);
    run server(servers[2]);

    run loadbalancer(loadbalancers[0],servers,servers[1],servers[2]);
    run loadbalancer(loadbalancers[1],servers[0],servers[1],servers[2])
  }
}
