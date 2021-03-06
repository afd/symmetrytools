byte initialised = 0

chan link1 = [ 1 ] of { pid , pid } 
chan link2 = [ 1 ] of { pid , pid } 
chan link3 = [ 1 ] of { pid , pid } 

chan null = [ 0 ] of { pid , pid } 
chan network = [ 2 ] of { pid , pid } 


inline lookup(id,link) {
   if
     :: id == 1 -> link = link1
     :: id == 2 -> link = link2
     :: id == 3 -> link = link3
  fi
}

proctype client(chan in) {

   pid sender ;
   pid receiver ;
   chan out ;
   d_step {
     out = network;
     initialised ++ 
   };
   initial : atomic {
      ( initialised == 3 && ( nempty ( in ) || nfull ( out ) ) ) ;
      if
        :: nempty ( in ) ->
        goto delivermail 
        :: empty ( in ) && nfull ( out ) ->
        goto sendmail 
      fi;
      delivermail : in ? sender , receiver ;
      assert ( receiver == _pid ) ;
      sender = 0 ;
      receiver = 0 ;
      goto initial ;
      sendmail :
        if
          :: receiver = 1
          :: receiver = 2
          :: receiver = 3
     fi;

     d_step {
         sender = _pid ;
         out ! sender , receiver ;
         sender = 0 ;
         receiver = 0 
      }
      ;
      goto initial 
   }
    
}

proctype mailer(chan in) {

   pid sender ;
   pid receiver ;
   chan deliverbox = null;
   loop : atomic {
      in ? sender , receiver ;
      lookup ( receiver , deliverbox ) ;
   };
   atomic {
      deliverbox ! sender , receiver ;
      deliverbox = null;
     sender = 0;
     receiver = 0;
      goto loop 
   }
    
}

init {
   atomic {
     run client(link1);
     run client(link2);
     run client(link3);
     run mailer(network);
   }
}
