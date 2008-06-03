mtype = {result}
chan client1=[1] of {mtype};
chan client2=[1] of {mtype};
chan client3=[1] of {mtype};
chan client4=[1] of {mtype};
chan client5=[1] of {mtype};
chan client6=[1] of {mtype};

chan server1=[3] of {chan};
chan server2=[3] of {chan};
chan server3=[3] of {chan};

chan loadbalancer1=[1] of {chan};
chan loadbalancer2=[1] of {chan};

chan null = [1] of {mtype}

proctype client(chan in, out) {
  do
    :: out!in
    :: in?result
  od
}

proctype server(chan in) {
  chan callback = null;
  do
    :: atomic {
      in?callback;
      callback!result;
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
    run client(client1,loadbalancers[0]);
    run client(client2,loadbalancers[0]);
    run client(client3,loadbalancers[0]);
    run client(client4,loadbalancers[1]);
    run client(client5,loadbalancers[1]);
    run client(client6,loadbalancers[1]);
    
    run server(server1);
    run server(server2);
    run server(server3);

    run loadbalancer(loadbalancer1,servers1,servers2,servers3);
    run loadbalancer(loadbalancer2,servers1,servers2,servers3)
  }
}
