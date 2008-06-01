mtype = {request,response,query,result};  /* The messages used in the model */
chan db_link = [0] of {mtype,chan}; /* Used by servers to send to the database */
chan cl_se_1 = [0] of {mtype,chan};  /* Input channels to the */
chan cl_se_2 = [0] of {mtype,chan};  /* three server          */
chan cl_se_3 = [0] of {mtype,chan};  /* processes             */
chan cl_se_4 = [0] of {mtype,chan};
chan cl1 = [0] of {mtype};
chan cl2 = [0] of {mtype};
chan cl3 = [0] of {mtype}; 
chan cl4 = [0] of {mtype}; 
chan cl5 = [0] of {mtype};
chan cl6 = [0] of {mtype};
chan cl7 = [0] of {mtype}; 
chan cl8 = [0] of {mtype}; 
chan cl9 = [0] of {mtype}; 
chan cl10 = [0] of {mtype}; 
chan cl11 = [0] of {mtype}; 
chan cl12 = [0] of {mtype}; 
chan cl13 = [0] of {mtype};
chan cl14 = [0] of {mtype};
chan cl15 = [0] of {mtype}; 
chan cl16 = [0] of {mtype}; 
chan cl17 = [0] of {mtype};
chan cl18 = [0] of {mtype};
chan cl19 = [0] of {mtype}; 
chan cl20 = [0] of {mtype}; 

chan se1 = [0] of {mtype};
chan se2 = [0] of {mtype};
chan se3 = [0] of {mtype};
chan se4 = [0] of {mtype};


chan null = [0] of {mtype}

proctype client(chan in; chan link) {
  do
    /* Send out a request and wait until a response is received */ 
    :: link!request,in;
       in?response
  od
}

proctype server(chan in; chan c_link) {
  chan current_client=null;
  do
    /* Receive a request from a client, send out a query to the
     database and then send a response back to the client */ 
    :: c_link?request,current_client;
       db_link!query,in;
       in?result;
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
    run database(db_link);
    run server(se1,cl_se_1);
    run server(se2,cl_se_2);
    run server(se3,cl_se_3);
    run server(se4,cl_se_4);

    run client(cl1,cl_se_1);
    run client(cl2,cl_se_1);
    run client(cl3,cl_se_1);
    run client(cl4,cl_se_1);
    run client(cl5,cl_se_1);

    run client(cl6,cl_se_2);
    run client(cl7,cl_se_2);
    run client(cl8,cl_se_2);
    run client(cl9,cl_se_2);
    run client(cl10,cl_se_2);

    run client(cl11,cl_se_3);
    run client(cl12,cl_se_3);
    run client(cl13,cl_se_3);
    run client(cl14,cl_se_3);
    run client(cl15,cl_se_3);

    run client(cl16,cl_se_4);
    run client(cl17,cl_se_4);
    run client(cl18,cl_se_4);
    run client(cl19,cl_se_4);
    run client(cl20,cl_se_4)

  }
}
