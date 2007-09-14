/* Finish inserting 'reset' macro calls, look at doing one for partnerid, and try removing asserts to see if this affects the state-space */

mtype = { on, off, st_idle, st_blocked, st_unobt, st_dial, st_busy }; 
chan null = [1] of {chan,bit}; 
chan zero = [1] of {chan,bit}; 
chan one = [1] of {chan,bit}; 
chan two = [1] of {chan,bit}; 
chan partner[3]

inline reset(messchan,messbit) { messchan = null; messbit = 0 }

proctype User (byte selfid; chan self) 
{
   /* start User */ 
   chan messchan = null; 
   bit messbit = 0; 
   mtype state = on; 
   mtype dev = on; 
   byte partnerid = 6; 

O_T_Null: 
   atomic 
   {
      assert( dev == on ); 
      assert(partner[selfid]==null); 
      /* either attempt a call, or receive one */ 
     if 
       :: empty(self) -> state=st_idle; 
          if 
            :: state==st_blocked -> state = on; goto O_T_Null
            :: else->state=on 
          fi; 
          dev=off;
          self!self,0;
          goto Auth_Orig_Att 
          /* no connection is being attempted, go offhook */ 
          /* and become originating party */ 
       :: full(self) -> self?<partner[selfid],messbit>;
          /* an incoming call */ 
          if 
            :: full(partner[selfid]) -> partner[selfid]?<messchan,messbit>; 
               if 
                 :: messchan==self /* call attempt still there */ 
                    -> reset(messchan,messbit); goto Present_Call 
                 :: else -> self?messchan,messbit; /* call attempt cancelled */ 
                    partner[selfid] = null;
                    partnerid = 6; messchan=null; messbit=0; goto Preidle 
               fi
            :: empty(partner[selfid]) ->
               self?messchan,messbit; /* call attempt cancelled */ 
               partner[selfid] = null; partnerid = 6;
               reset(messchan,messbit); goto Preidle 
          fi 
     fi
   }; 

Auth_Orig_Att: 
   atomic 
   {
      assert(dev == off); 
      assert(full(self)); 
      assert(partner[selfid]==null); 

      /* dialing or go onhook */ 
      if 
        :: /* dial and then nondeterministic choice of called party */ 
           if 
             :: partner[selfid] = zero; 
                partnerid = 0 
             :: partner[selfid] = one; 
                partnerid = 1 
             :: partner[selfid] = two; 
                partnerid = 2 
             :: partnerid = 7; 
           fi; 
           state = st_dial;
           if
             :: (state==st_dial && partnerid!=7) -> state = on; goto Call_Sent 
             :: (state==st_dial && partnerid==7) -> state = on;
                partner[selfid] = null; partnerid=6; 
                goto O_T_Disconnect 
           fi 
        :: dev = on;
           self?messchan,messbit;
           assert(messchan==self); 
           reset(messchan,messbit); goto Preidle 
           /*go onhook, without dialing */ 
      fi
   }; 

Call_Sent: /* check number called and process */ 
   atomic 
   {
      assert(dev == off); 
      assert(full(self)); 
      state = on; 
      if 
        :: partner[selfid] == self ->
           goto O_Busy /* invalid partner */ 
        :: partner[selfid]!=self -> 
           if 
             :: empty(partner[selfid]) -> 
                partner[selfid]!self,0;
                self?messchan,messbit; 
                self!partner[selfid],0;
                reset(messchan,messbit);
                goto O_Alerting 
                /* valid partner, write token to partner's channel*/ 
             :: full(partner[selfid]) -> goto O_Busy 
                /* valid partner but engaged */ 
           fi 
      fi
   }; 

O_Busy: /* number called is engaged, go onhook or trivial dial */ 
   atomic 
   {
      assert(full(self)); 
      if 
        :: state = st_busy; 
           state = on; 
           dev = on;
           self?messchan,messbit;
           assert(messchan==self); 
           partner[selfid] = null;
           partnerid = 6;
           reset(messchan,messbit);
           goto Preidle 
           /*go onhook, cancel connection attempt */ 
      fi
   }; 

O_T_Disconnect: /* number called is unobtainable, go onhook or trivial dial */ 
   atomic 
   {
      assert(full(self)); 
      assert(partner[selfid]==null);
      assert(partnerid==6); 
      if 
        :: dev = on;
           self?messchan,messbit;
           assert (messchan==self); 
           reset(messchan,messbit);
           goto Preidle 
           /* go onhook, cancel connection attempt */
      fi
   }; 

O_Alerting: /* called party is ringing */ 
   atomic 
   {
      assert(full(partner[selfid])); 
      assert(full(self)); assert(dev == off); 
      self?<messchan,messbit>;
      assert(messchan==partner[selfid]);
      messchan=null; 

      /* check channel */ 
      if 
        :: messbit==1 ->
           messbit = 0;
           goto O_Active 
           /* correct token */ 
        :: messbit==0 ->
           goto O_Alerting 
           /* wrong token, not connected yet, try again */ 
        :: messbit==0 ->
           goto O_No_Answer 
           /* give up */ 
      fi
   }; 


O_No_Answer: /*abandon call attempt*/ 
   atomic 
   {
      assert(full(partner[selfid]));
      assert(full(self)); 
      assert(dev == off); 
      dev = on;
      self?messchan,messbit; 
      partner[selfid]?messchan,messbit; partner[selfid]!messchan,0; 
      partner[selfid]=null;partnerid=6; 
      reset(messchan,messbit);
      goto Preidle; 
      /* give up, go onhook */ 
   }; 

O_Active: 

   atomic 
   {
      assert(full(self)); assert(full(partner[selfid])); 
      /* connection established */ 
      goto O_Close
   }; 

O_Close: /* disconnect call */ 
   atomic 
   {
      assert(full(self));
      assert(full(partner[selfid])); 
      dev = on;
      self?messchan,messbit; /* empty own channel */ 
      assert(messchan==partner[selfid]);
      assert(messbit==1); 
      partner[selfid]?messchan,messbit; /* empty partner's channel */ 
      assert(messchan==self);
      assert(messbit==1); 
      /* and disconnect partner */ 
      partner[selfid]!messchan,0; 
      partner[selfid]=null; 
      partnerid=6;
      messchan=null;
      messbit=0; 
      goto Preidle
   }; 

Present_Call: 
   atomic 
   {
      assert((dev == on)&&(full(self))); 
      /* either device rings or connection attempt is cancelled and then empty channel */ 
      partner[selfid]?<messchan,messbit>; 
      if 
        :: messchan==self -> 
           reset(messchan,messbit);
           goto T_Alerting 
        :: else -> skip /* attempt has been cancelled */ 
      fi; 
      self?messchan,messbit; 
      partner[selfid] = null;
      partnerid = 6;
      reset(messchan,messbit);
      goto Preidle 
   }; 

T_Alerting: /* proceed with connection or connect attempt cancelled */ 
   atomic 
   {
      assert(full(self)); 
      if 
        :: full(partner[selfid]) ->
           partner[selfid]?<messchan,messbit>; 
           if 
             :: messchan==self -> /*connection proceeding */ 
                assert(messbit==0); 
                self?messchan,messbit; 
                assert(messchan==partner[selfid]);
                assert(messbit==0); 
                dev = off;
                partner[selfid]?messchan,messbit; 
                partner[selfid]!self,1; /* establish connection */ 
                self!partner[selfid],1;
                messchan=null;
                messbit=0;
                goto T_Active 
             :: else -> /* wrong message, connection cancelled */ 
                self?messchan,messbit; 
                dev=on;
                partner[selfid] = null;
                partnerid=6;
                messchan=null;
                messbit=0; 
                goto Preidle 
           fi 
        :: empty(partner[selfid]) -> /* connection cancelled */ 
           self?messchan,messbit; 
           dev = on;
           partner[selfid] = null;
           partnerid = 6; 
           reset(messchan,messbit);
           goto Preidle 
      fi 
   }; 

T_Active: /* check if originator has terminated call */ 
   atomic 
   {
      self?<messchan,messbit>; 
      if 
        :: (messbit==1 && dev==off) -> /* trivial handset down */ 
           dev = on;
           reset(messchan,messbit);
           goto T_Active 
        :: (messbit==1 && dev==on) -> /* trivial handset up */ 
           dev = off;
           messchan=null;
           messbit=0;
           goto T_Active 
        :: (messbit==0 && dev==on) -> /* connection is terminated */ 
           self?messchan,messbit; 
           partner[selfid] = null;
           partnerid=6;
           reset(messchan,messbit);
           goto Preidle 
        :: (messbit==0 && dev==off) -> 
           /* disconnect tone */ 
           dev=on; /* connection is terminated */ 
           self?messchan,messbit;
           partner[selfid] = null; 
           partnerid = 6;
           reset(messchan,messbit);
           goto Preidle 
      fi 
   }; 

Preidle:
   atomic /* Do we need a skip here? - ALLY */
   {
      goto O_T_Null 
   } 

} /* end User */ 

init 
{ 
   atomic 
   {
      partner[0]=null;
      partner[1]=null;
      partner[2]=null;

      run User(0,zero); 
      run User(1,one); 
      run User(2,two); 
   } 
}

