/* Finish inserting 'reset' macro calls, look at doing one for partnerid, and try removing asserts to see if this affects the state-space */

mtype = { on, off, st_idle, st_blocked, st_unobt, st_dial, st_busy }; 
chan null = [1] of {chan,bit}; 
chan zero = [1] of {chan,bit}; 
chan silly = [0] of {chan,bit};
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

Call_Sent:
   atomic 
   {
      assert(dev == off); 
      assert(full(self)); 
      state = on; 
      if 
        :: partner[selfid] == self ->
           goto O_Busy  
        :: partner[selfid]!=silly -> 
           if 
             :: empty(partner[selfid]) -> 
                partner[selfid]!silly,self;
                self?messchan,messbit; 
                self!partner[selfid],0;
                reset(messchan,messbit);
                goto O_Alerting 

             :: full(partner[selfid]) -> goto O_Busy 

           fi 
      fi
   }; 

} /* end User */ 

