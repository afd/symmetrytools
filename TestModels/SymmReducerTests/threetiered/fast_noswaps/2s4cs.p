mtype = {request,response,query,result};
chan database_link = [2] of {mtype,chan};
chan server0_link = [1] of {mtype,chan};
chan server1_link = [1] of {mtype,chan};
chan clients0 = [1] of {mtype};
chan clients1 = [1] of {mtype};
chan clients2 = [1] of {mtype};
chan clients3 = [1] of {mtype};
chan clients4 = [1] of {mtype};
chan clients5 = [1] of {mtype};
chan clients6 = [1] of {mtype};
chan clients7 = [1] of {mtype};

chan servers0 = [1] of {mtype};
chan servers1 = [1] of {mtype};

chan null = [0] of {mtype}

proctype client(chan in; chan link) {
  do
    /* Send out a request and wait until a response is received */ 
    :: link!request,in;
       in?response
  od
}

proctype server(chan db_in; chan c_link, db_link) {
  chan current_client=null;
  do
    /* Receive a request from a client, send out a query to the
     database and then send a response back to the client */ 
    :: c_link?request,current_client;
       db_link!query,db_in;
       db_in?result;
       current_client!response;
       current_client=null
  od
}

proctype database(chan link) {
  chan current_server=null;
  do
    /* Receive a query from a server and send back a result */
    :: link?query,current_server;
       current_server!result;
       current_server=null
  od
}

init {
  atomic {
    /* Run the database, server and client processes */
    run database(database_link);
    run server(servers0,server0_link,database_link);
    run server(servers1,server1_link,database_link);
    run client(clients0,server0_link);
    run client(clients1,server0_link);
    run client(clients2,server0_link);
    run client(clients3,server0_link);
    run client(clients4,server1_link);
    run client(clients5,server1_link);
    run client(clients6,server1_link);
    run client(clients7,server1_link);
  }
}
