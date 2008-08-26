mtype = {nullmsg,request,response};

chan load_balancer_in = [4] of {mtype,chan};

chan servers0 = [2] of {mtype,chan};
chan servers1 = [2] of {mtype,chan};

chan clients0 = [1] of {mtype};
chan clients1 = [1] of {mtype};
chan clients2 = [1] of {mtype};
chan clients3 = [1] of {mtype};

chan null = [0] of {mtype}

proctype client(chan in) {
  do
    :: load_balancer_in!request,in;
       in?response
  od
}

proctype loadBalancer() {
  mtype msg = nullmsg;
  chan link = null;
  do
    :: load_balancer_in?msg,link;
       if
	 :: len(servers0)<=len(servers1) -> servers0!msg,link
	 :: len(servers1)<=len(servers0) -> servers1!msg,link
       fi;
       msg = nullmsg;
       link = null
  od
}

proctype server(chan in) {
  chan current_client = null;
  do
    :: in?request,current_client;
       current_client!response;
       current_client = null
  od
}

init {
  atomic {
    run loadBalancer();
    run client(clients0);
    run client(clients1);
    run client(clients2);
    run client(clients3);
    run server(servers0);
    run server(servers1);
  }
}
