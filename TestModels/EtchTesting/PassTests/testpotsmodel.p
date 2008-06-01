/* 4 users model with 0 features generated from Template */ 

/* Alice Miller and Muffy Calder*/

/*  Messages have 2 parts: channel name and status of connection */
/*  Channel name is the name of the party involved in the *
/*  potential connection. Status (0,1) denotes whether or not */
/*  connection has happened */ 

/* Each user process has a communication channel which can contain */
/* at most one message. */
/* Meaning of contents of user A's communication channel: 	*/	
/*	empty 	- A is free					*/
/*	A,0	- A is engaged, but not connected.		*/
/*		  A is originating party.			*/
/*	B,0	- A is engaged, but not connected.		*/
/*		  A is terminating party; 			*/
/*		  B is attempting connection 			*/
/* 	X,1	- if X's channel contains A,1, then		*/
/*		  X and A are connected.			*/

mtype = {on,off,dial,call,oring,tring,unobt,engaged,connected,disconnect,ringbackev,ret_alert,st_idle,st_blocked,st_unobt,st_rback1,st_rback2,st_diall,st_call1,st_call2,st_preidle,st_redial,st_busy}

chan zero = [1] of {chan,bit};
chan one = [1] of {chan,bit};
chan two = [1] of {chan,bit};
chan three = [1] of {chan,bit};

chan null = [1] of {chan,bit};
chan chan_name[4]; /*convert from number to channel name*/

chan partner[4]

/* The simple basic call protocol: A rings B			*/
/* A goes offhook, put A,0 on channel A  			*/
/* A dials B and B is free, 					*/
/* then A puts A,0 on channel B; B,0 on channel A.           */
/* B goes offhook and then put B,1 on channel A	        */
/* A and B are now connected					*/
/* To disconnect: A removes token from own channel, 		*/
/*  B removes token from own channel 			*/

proctype User (byte selfid;chan self) {
  chan messchan=null;
  bit messbit=0;
  mtype state=on;
  mtype dev=on;
 
  byte partnerid=6;
idle:
  atomic {
    assert(dev==on);
    assert(partner[selfid]==null);
    assert(state==on);
    assert(partnerid==6);

    /* either attempt a call, or receive one */
    if
      :: (len(self)==0)->
	 state=st_idle;
	 if
	   :: else->state=on
	 fi;
	 dev=off;
	 self!self,0;goto diall
	 /* no connection is being attempted, go offhook */
	 /* and become originating party */

      :: (len(self)==1)-> self?<partner[selfid],messbit>;
	 /* an incoming call */ 
	 if :: (len(partner[selfid])==1)->
	       partner[selfid]?<messchan,messbit>;/*partner-polling*/
	       if 
		 :: messchan == self ->/* call attempt still there */
		    messchan=null;messbit=0;goto talert 
		 :: else -> self?messchan,messbit;  /* call attempt cancelled */
			    partner[selfid]=null;partnerid=6;messchan=null;messbit=0;
			    goto preidle
               fi
	    :: (len(partner[selfid])==0)->
	       self?messchan,messbit;  /* call attempt cancelled */
	       partner[selfid]=null;partnerid=6;messchan=null;messbit=0;
	       goto preidle
	 fi
    fi
  };
  
diall:
  atomic {
    assert(dev==off);
    assert(full(self));
    assert(partner[selfid]==null);
    /* dial or go onhook */
    if
      :: 
	 /* dial and then nondeterministic choice of called party */
         if
	   
	   :: partner[selfid]=zero; 
	      partnerid=0
	   :: partner[selfid]=one;
	      partnerid=1
	   :: partner[selfid]=two;
	      partnerid=2
	   :: partner[selfid]=three; 
	      partnerid=3
	   :: partnerid= 7
	 fi;
	 state=st_diall;
	 /*no call to feature_lookup required */
	 if
	   ::state==st_unobt->
	      state=on;partner[selfid]=null;partnerid=6;
	      goto unobtainable
	   ::(state==st_diall&&partnerid!=7)->
	      state=on;
	      goto calling
	   ::(state==st_diall&&partnerid==7)->
	      state=on;partner[selfid]=null;partnerid=6;
	      goto unobtainable
	   ::(state==st_redial)->
	      state=on;
	      partnerid=6;
	      goto diall
	 fi
      ::
	 dev=on;
	 self?messchan,messbit;
	 assert(messchan==self);
	 messchan=null;messbit=0;
	 goto preidle
	 /*go onhook, without dialling */
    fi
  };

calling:/* check number called and process */
  atomic {
    assert(dev==off);
    assert(full(self));
    state=st_call2;
    /*no call to feature_lookup required */
    if
      ::state==st_unobt->
	 state=on;partner[selfid]=null;partnerid=6;
	 goto unobtainable
      ::state==st_call2->
	 state=on;skip
    fi;
    if
      :: partner[selfid] == self ->
	 goto busy
	 /* invalid partner */
      :: partner[selfid]!=self -> 
	 if ::(len(partner[selfid])==1)->             
	       goto busy
	       /* valid partner but engaged */
	    ::(len(partner[selfid])==0) ->
	       partner[selfid]!self,0; /* calling-partner */
	       self?messchan,messbit;
	       self!partner[selfid],0;
	       messchan=null;messbit=0; goto oalert
	       /* valid partner, write token to partner's channel*/
	 fi
    fi
  };


busy: /* number called is engaged, go onhook or trivial dial */
  atomic {
    assert(full(self));
    if  
      :: state=st_busy;
	 /*no call to feature_lookup required */
	 state=on;
	 dev=on;
	 self?messchan,messbit;
	 assert(messchan==self);
	 partner[selfid]=null;partnerid=6;
	 messchan=null;
	 
	 messbit=0; goto preidle
         /*go onhook, cancel connection attempt */ 
	 /* :: event_action(dial);
	      goto busy*/
         /* trivial dial */
      fi
  };
  
  /*comment out entire ringback state when no ringback feature  switched on */
  
  /* ringback state not required */
  
  
unobtainable:/* number called is unobtainable, go onhook or trivial dial */
  atomic{
    assert(full(self));
    assert(partner[selfid]==null);
    assert(partnerid==6);
    if
      :: dev=on;  
	 self?messchan,messbit;
	 assert(messchan==self);
	 messchan=null;
	 messbit=0;goto preidle
         /*go onhook, cancel connection attempt */ 
         /*::event_action(dial);goto busy*/
         /* trivial dial */
    fi
  }; 
  
  
oalert:
  /* called party is ringing */ 
  atomic{
    assert(full(partner[selfid]));
    assert(full(self));
    assert(dev==off);
    
    self?<messchan,messbit>;/*self-polling*/
    assert(messchan==partner[selfid]);
    messchan=null;
    /* check channel */
    if
      :: messbit== 1->messbit=0;goto oconnected 
		     /* correct token */
      :: messbit==0->goto oalert
           /* wrong token, not connected yet, try again */
      :: messbit==0->goto oringout 
		     /* give up */
		     /* :: event_action(dial);messbit=0;goto oalert*/
		     /* trivial dial */
    fi
  };
        

oringout:/*abandon call attempt*/
  atomic {
    assert(full(partner[selfid]));
    assert(full(self));
    assert(dev==off);
    dev=on;
    self?messchan,messbit;
    partner[selfid]?messchan,messbit; partner[selfid]!messchan,0;/*finish-call*/
    partner[selfid]=null;partnerid=6;
    
    messchan=null;messbit=0;
    goto preidle
    /* give up, go onhook */
  };
  
oconnected:
  atomic {
    assert(full(self));
    assert(full(partner[selfid]));
    /* connection established */
    
    
    goto oclose
  };
  
  
oclose:/* disconnect call */
  atomic{
    assert(full(self));
    assert(full(partner[selfid]));
    
    dev=on; 
    self?messchan,messbit;                   /* empty own channel */
    assert(messchan==partner[selfid]);
    assert(messbit==1);  
    partner[selfid]?messchan,messbit;partner[selfid]!messchan,0; /*finish-call*/
    assert(messchan==self);
    assert(messbit==1);
    /* and disconnect partner */
    
    
    
    partner[selfid]=null;
    
    partnerid=6;messchan=null;messbit=0;
    goto preidle};
  
  
talert:atomic{
  assert(dev==on);
  assert(full(self));
  /* either device rings or*/
  /* connection attempt is cancelled and then empty channel */
  partner[selfid]?<messchan,messbit>;/*partner-polling*/
  if
    :: messchan==self->
       
       messchan=null;messbit=0;
       goto tpickup
    :: else->skip /* attempt has been cancelled */
  fi;
  
  self?messchan,messbit;
  partner[selfid]=null;partnerid=6;
  
  messchan=null;messbit=0;
	       goto preidle
};
  
  
tpickup:/* proceed with connection or connect attempt cancelled */
  atomic{assert(full(self));
	 if ::(len(partner[selfid])==1)-> 
	       partner[selfid]?<messchan,messbit>;/*partner-polling*/
                      if 
                        :: messchan==self -> /*connection proceeding */
			   assert(messbit==0);
			   self?messchan,messbit;
			   assert(messchan==partner[selfid]);
			   assert(messbit==0);
			   
		              dev=off;
			   partner[selfid]?messchan,messbit; partner[selfid]!self,1; /*confirm-call*/
			   /* establish connection */
		              self!partner[selfid],1;
			   messchan=null;
			   messbit=0;
			   goto tclose
                        :: else ->   /* wrong message, connection cancelled */
			   
                           self?messchan,messbit;
			   
			   dev=on;
			   partner[selfid]=null;
			   
			   partnerid=6;messchan=null;messbit=0;
			   goto preidle
	       fi
	       
	    :: (len(partner[selfid])==0)-> /* connection cancelled */
	       
	       self?messchan,messbit;
	       
	       dev=on;
	       partner[selfid]=null;partnerid=6;
	       
	       messchan=null;messbit=0;  
	       goto preidle
	 fi};
  
  
tclose:/* check if originator has terminated call */
  

  atomic{
    self?<messchan,messbit>;/*self-polling*/
    if 
      ::(messbit==1 &&
	 dev==off
      ) -> /* trivial handset down */
	 
	 dev=on;
	 messchan=null;messbit=0;goto tclose                       
	 
      ::(messbit==1 &&
	 dev==on
      ) ->  /* trivial handset up */
	 
	 dev=off;
	 messchan=null;messbit=0;goto tclose                           
      :: (messbit==0 && dev==on) -> /* connection is terminated 
	   */
	 self?messchan,messbit;
	 partner[selfid]=null;partnerid=6;
	 
	 messchan=null;messbit=0;
	 goto preidle       
      :: (messbit==0 && dev==off) ->
	 
	 /* disconnect tone */
	 
	 dev=on;
	 /* connection is terminated 
*/
                            self?messchan,messbit;
	       partner[selfid]=null;
	       
	       partnerid=6;messchan=null;messbit=0;
	       goto preidle  
                                                              
	       fi};

preidle:
	atomic{
	   
	       
   goto idle
}	
 
} /* end User */



   
/* no hash-definition required */
   
init
{     
 atomic{partner[0]=null;
partner[1]=null;
partner[2]=null;
partner[3]=null;

	chan_name[0]=zero;
chan_name[1]=one;
chan_name[2]=two;
chan_name[3]=three;

	
 /*switch on features here*/
 /*default value 6, */
 /*if user i has feature, set to id of user to be forwarded to, or screened */
 /*otherwise, if appropriate set to 0 or 1 corresponding to feature on or off*/
        
	run User(3,three);
	
run User(0,zero);
run User(1,one);
run User(2,two);

     }
}










































































