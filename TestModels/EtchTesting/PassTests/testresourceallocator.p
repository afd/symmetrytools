/* Model of a resource allocator with a random allocation policy
   Alastair Donaldson
   Last modified 01/10/03
*/
 
mtype = {request,confirmation,finished}
chan client_channels = [1] of {mtype};
byte resource_user = 255;
byte priorities[3]

proctype client(byte id) {

  do
    :: client_channels[id]!request;
       atomic { client_channels[id]?confirmation; resource_user = id };
       atomic { client_channels[id]!finished; resource_user = 255 }
  od
  
}

proctype resource_allocator() {

  byte chosen_client = 255;
  byte chosen_priority = 0;
  byte counter = 0;
    
  do
    ::
       atomic {
	 (client_channels[0]?[request]||client_channels[1]?[request]||client_channels[2]?[request]);

	 do
	   :: (counter==3) -> break
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

	 client_channels[chosen_client]?request;
	 client_channels[chosen_client]!confirmation;
	 counter = 0;
	 chosen_priority = 0
	 
       };
       
       atomic { client_channels[chosen_client]?finished; chosen_client = 255 }
       
  od
  
}

init {
  
  atomic {
    
    priorities[0] = 2;
    priorities[1] = 2;
    priorities[2] = 2;
    
    run client(0);
    run client(1);
    run client(2);
    
    run resource_allocator()
    
  }
  
}
