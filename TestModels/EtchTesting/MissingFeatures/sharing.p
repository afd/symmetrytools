/* Model of a resource allocator with a priority based allocation policy
   and sharing between client processes */
 
#define NO_OF_CLIENTS 7
#define NO_ONE 255

mtype = {request,confirmation,finished};              /* Messages used by the basic protocol */
chan client_channels[NO_OF_CLIENTS] = [1] of {mtype}; /* The communication channels in the model */
byte resource_user = NO_ONE;                          /* Holds the id of the current user of the resource */
byte priorities[NO_OF_CLIENTS];                       /* Holds the priority level of each client */
byte shareswith[NO_OF_CLIENTS] = NO_ONE;              /* Used to implement sharing between clients */ 

proctype client(byte id) {

  do
    /* Send a request, receive a confirmation and use the resource */
    :: client_channels[id]!request;
       atomic { client_channels[id]?confirmation; resource_user = id }
       
       if
	 :: (shareswith[id]!=NO_ONE) -> if
					  /* If this process shares with another process and that process has sent a request
					   then service that request */
					  :: atomic
					     { client_channels[shareswith[id]]?[request] ->
					       resource_user = NO_ONE;
					       client_channels[shareswith[id]]?request
					     }
					     client_channels[shareswith[id]]!confirmation;
					     client_channels[shareswith[id]]?finished;
					  :: else -> skip
					fi
					     :: else skip
       fi;

       /* Send a finished message back to the resource allocator */
       atomic { resource_user = NO_ONE; client_channels[id]!finished }
  od
  
}

proctype resource_allocator() {

  byte chosen_client = NO_ONE; /* Used to decide which client request to service */
  byte chosen_priority = 0;    /* Used to ascertain the highest priority request */
  byte counter = 0;
  
  
  do
    ::
       atomic {
	 /* The resource allocator blocks until there is at least one request waiting to be serviced */
	 (client_channels[0]?[request]||client_channels[1]?[request]||client_channels[2]?[request]||
	  client_channels[3]?[request]||client_channels[4]?[request]||client_channels[5]?[request]||
	  client_channels[6]?[request]);

	 do
	   /* One of the highest priority requests is chosen to be serviced */
	   :: (counter==NO_OF_CLIENTS) -> break
	   :: else -> if
			:: client_channels[counter]?[request] ->
			   if
			     :: (chosen_client==NO_ONE)||(priorities[counter]>=chosen_priority) -> chosen_client = counter;
												   chosen_priority = priorities[counter]
			     :: (chosen_client!=NO_ONE)&&(priorities[counter]<=chosen_priority) -> skip
			   fi
			:: else -> skip
		      fi;
		      counter++
	 od;

	 /* A request is received from the chosen client, and a confirmation sent back */
	 client_channels[chosen_client]?request;
	 client_channels[chosen_client]!confirmation;
	 counter = 0;
	 chosen_priority = 0;
	 
       }

       /* On receiving a finished message the resource allocator can give the resource out again */
       atomic { client_channels[chosen_client]?finished; chosen_client = NO_ONE }
       
  od
  
}

init {
  
  atomic {
    
    /* Set up the priorities */ 
    priorities[0] = 2;
    priorities[1] = 2;
    priorities[2] = 1;
    priorities[3] = 1;
    priorities[4] = 1;
    priorities[5] = 0;
    priorities[6] = 0;

    /* Set up the sharing */
    shareswith[2] = 3;
    
    /* Run the clients and the resource allocator */        
    run client(0);
    run client(1);
    run client(2);
    run client(3);
    run client(4);
    run client(5);
    run client(6);
 
    run resource_allocator()
    
  }
  
}
