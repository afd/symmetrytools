/* Model of a resource allocator with a priority based allocation policy */
 
mtype = {request,confirmation,finished};              /* Messages used by the basic protocol */
chan client_channels[7] = [1] of {mtype}; /* The communication channels in the model */
byte resource_user = 255;                          /* Holds the id of the current user of the resource */
byte priorities[7]                       /* Holds the priority level of each client */

proctype client(byte id) {

  do
    /* Send a request, receive a confirmation, use the resource and send a finished message */
    :: client_channels[id]!request;
       atomic { client_channels[id]?confirmation; resource_user = id };
       atomic { resource_user = 255; client_channels[id]!finished }
  od
  
}

proctype resource_allocator() {

  byte chosen_client = 255; /* Used to decide which client request to service */
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
	   :: (counter==7) -> break
	   :: else -> if
			:: client_channels[counter]?[request] ->
			   if
			     :: (chosen_client==255)||(priorities[counter]>=chosen_priority) -> chosen_client = counter;
												  chosen_priority = priorities[counter]
			     :: (chosen_client!=255)&&(priorities[counter]<=chosen_priority) -> skip
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
	 
       };

       /* On receiving a finished message the resource allocator can give the resource out again */
       atomic { client_channels[chosen_client]?finished; chosen_client = 255 }
       
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
