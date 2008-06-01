mtype = {request,response,query,result}
chan database_link = [1] of {mtype,chan};
chan server0_link = [1] of {mtype,chan};
chan server1_link = [1] of {mtype,chan};
chan clients0 = [1] of {mtype};
chan clients1 = [1] of {mtype};
chan clients2 = [1] of {mtype};
chan clients3 = [1] of {mtype};
chan clients4 = [1] of {mtype};
chan clients5 = [1] of {mtype};

chan servers0 = [1] of {mtype};
chan servers1 = [1] of {mtype}

proctype client(chan out, in) {
  do

    :: out!request,in;
       in?response
  od
}

proctype server(chan c_link, db_link, in) {
  chan current_client;
  do


    :: c_link?request,current_client;
       db_link!query,in;
       in?result;
       current_client!response
  od
}

proctype database(chan link) {
  chan current_server;
  do

    :: link?query,current_server;
       current_server!result
  od
}

init {
  atomic {

    run database(database_link);
    run server(server0_link,database_link,servers0);
    run server(server1_link,database_link,servers1);
    run client(server0_link,clients0);
    run client(server0_link,clients1);
    run client(server0_link,clients2);
    run client(server1_link,clients3);
    run client(server1_link,clients4);
    run client(server1_link,clients5)
  }
}
