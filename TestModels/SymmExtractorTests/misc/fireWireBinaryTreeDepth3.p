/*Leader Election model with 3 processes */ 
/*Generated from template*/ 
/*With collective acknowledgements*/ 
/* Leader Election in IEEE */
/*Including optimisation */
/*acyclic configuration*/
/*including collective acknowledgements*/

mtype = {nullmessage,be_my_parent,be_my_child,ack,ack_b};

pid elected=8;

byte adj[8]

typedef array {
  bool to[8] = false
}

hidden array connect[8];

byte toss[8]=0;

chan nullchan = [0] of {mtype};

hidden byte waited_for[8];


hidden pid current;

/*define the channels, need to change per configuration*/

chan onetwo=[1] of {mtype}; 
chan twoone=[1] of {mtype}; 
chan onethree=[1] of {mtype}; 
chan threeone=[1] of {mtype}; 
chan twofour=[1] of {mtype}; 
chan fourtwo=[1] of {mtype}; 
chan twofive=[1] of {mtype}; 
chan fivetwo=[1] of {mtype}; 
chan threesix=[1] of {mtype}; 
chan sixthree=[1] of {mtype}; 
chan threeseven=[1] of {mtype}; 
chan seventhree=[1] of {mtype}

inline converter(id1,id2,chanin,chanout) {
  if 
    :: (id1==1)-> assert((id2==2)||(id2==3));
       if 
	 ::(id2==2)->chanin=twoone;chanout=onetwo
	 ::(id2==3)->chanin=threeone;chanout=onethree
		  fi 
		  
    :: (id1==2)-> assert((id2==1)||(id2==4)||(id2==5));
       if 
	 ::(id2==1)->chanin=onetwo;chanout=twoone
	 ::(id2==4)->chanin=fourtwo;chanout=twofour
	 ::(id2==5)->chanin=fivetwo;chanout=twofive
		  fi 
		  
    :: (id1==3)-> assert((id2==1)||(id2==6)||(id2==7));
       if 
	 ::(id2==1)->chanin=onethree;chanout=threeone
	 ::(id2==6)->chanin=sixthree;chanout=threesix
	 ::(id2==7)->chanin=seventhree;chanout=threeseven
		  fi 
		  
    :: (id1==4)-> assert((id2==2));
		  chanin=twofour;chanout=fourtwo
		  
    :: (id1==5)-> assert((id2==2));
		  chanin=twofive;chanout=fivetwo
		  
    :: (id1==6)-> assert((id2==3));
		  chanin=threesix;chanout=sixthree
		  
    :: (id1==7)-> assert((id2==3));
		  chanin=threeseven;chanout=seventhree
		  
  fi
}

inline find_remaining(id1,id2) {
  /*takes an id and returns partner that is not a child*/
  if :: connect[id1].to[1] && (!(child[0]==1 || child[1]==1)) -> id2 = 1
     :: connect[id1].to[2] && (!(child[0]==2 || child[1]==2)) -> id2 = 2
     :: connect[id1].to[3] && (!(child[0]==3 || child[1]==3)) -> id2 = 3
     :: connect[id1].to[4] && (!(child[0]==4 || child[1]==4)) -> id2 = 4
     :: connect[id1].to[5] && (!(child[0]==5 || child[1]==5)) -> id2 = 5
     :: connect[id1].to[6] && (!(child[0]==6 || child[1]==6)) -> id2 = 6
     :: connect[id1].to[7] && (!(child[0]==7 || child[1]==7)) -> id2 = 7
  fi
}

inline poll(current) {
  assert(current!=_pid);
  converter(_pid,current,self_in,self_out);
  if
    :: self_in?message;
       assert(message==be_my_parent);
       child[counter]=current;
       counter++;
       message = nullmessage;
    :: empty(self_in)
       
  fi;
  self_in = nullchan;
  self_out = nullchan;
  waited_for[current] = 1
}

proctype node() {
  mtype message=nullmessage;
  pid child[2] = 0;
  pid remaining_partner=0;
  pid partnerid=0;
  byte counter=0;
  byte no_of_requests=0;
  chan self_in=nullchan;
  chan self_out=nullchan;

  assert(!connect[_pid].to[_pid]);
  
start:
  atomic {
   assert((counter==0)&&(message==nullmessage)&&(partnerid==0)&&(self_in==nullchan)&&(self_out==nullchan));
   if :: (adj[_pid]==1)->
	 goto parent_request
      :: else->
	 goto wait_for_request
   fi
 };

parent_request:
  atomic {
    assert((partnerid==0)&&(message==nullmessage)&&(self_in==nullchan)&&(self_out==nullchan)&&(counter<8));

    if
      :: (_pid!=1)&&(connect[_pid].to[1])->partnerid=1; goto found_partner1
      :: (_pid!=2)&&(connect[_pid].to[2])->partnerid=2; goto found_partner1
      :: (_pid!=3)&&(connect[_pid].to[3])->partnerid=3; goto found_partner1
      :: (_pid!=4)&&(connect[_pid].to[4])->partnerid=4; goto found_partner1
      :: (_pid!=5)&&(connect[_pid].to[5])->partnerid=5; goto found_partner1
      :: (_pid!=6)&&(connect[_pid].to[6])->partnerid=6; goto found_partner1
      :: (_pid!=7)&&(connect[_pid].to[7])->partnerid=7; goto found_partner1
    fi
  };
       
found_partner1:
  atomic {
    assert((partnerid!=_pid)&&(self_in==nullchan)&&(self_out==nullchan)&&(message==nullmessage));
    converter(_pid,partnerid,self_in,self_out);
    if
      :: self_in?message->
	 assert(message==be_my_parent);
	 message=nullmessage;
	 no_of_requests=1;
	 adj[_pid]=1;
	 child[0]=partnerid;
	 partnerid=0;
	 counter=0;
	 goto child_handshake
      :: empty(self_in)->
	 assert(empty(self_out));
	 self_out!be_my_parent;
	 goto response
    fi
  };

 response:
     atomic{full(self_in);assert((message==nullmessage)&&(counter==0));self_in?            message;
            if
	    ::message==be_my_child->message=nullmessage;partnerid=0;
	      goto become_child
	    ::message==be_my_parent->message=nullmessage;
	      goto contention
            fi};

 become_child:atomic
	  {empty(self_out);
           self_out!ack;
           assert((message==nullmessage)&&(counter==0)&&(partnerid==0));
	  self_in=nullchan;
	  self_out=nullchan;
           goto finish};



contention:
  atomic {
    assert((message==nullmessage)&&(counter==0)&&(partnerid!=0));
    if
      ::(toss[_pid]==0 && toss[partnerid]==0) ->
	 toss[_pid]++;
	 toss[partnerid]++;
	 goto winner
      :: else->
	 assert(toss[_pid]==1 && toss[partnerid]==1);
	 toss[_pid]=0;
	 toss[partnerid]=0;
	 goto loser
    fi
  };

winner:
  atomic {
    empty(self_out);
    self_out!be_my_parent;
    goto response
  };

loser:
  atomic {
    self_in?message->
    assert(message==be_my_parent);
    message=nullmessage;
    no_of_requests=1;
    adj[_pid]=1;
    child[0]=partnerid;
    partnerid=0;
    goto child_handshake
  };
		 
wait_for_request:
  atomic{
    assert((partnerid==0)&&(self_in==nullchan)&&(self_out==nullchan)&&(message==nullmessage)&&(counter<=adj[_pid]));

    do
      :: waited_for[1]!=0 -> waited_for[1] = 0;
      :: waited_for[2]!=0 -> waited_for[2] = 0;
      :: waited_for[3]!=0 -> waited_for[3] = 0;
      :: waited_for[4]!=0 -> waited_for[4] = 0;
      :: waited_for[5]!=0 -> waited_for[5] = 0;
      :: waited_for[6]!=0 -> waited_for[6] = 0;
      :: waited_for[7]!=0 -> waited_for[7] = 0;
      :: else
    od;
    
    do
      :: connect[_pid].to[1] && waited_for[1]==0 -> current = 1; poll(current);
      :: connect[_pid].to[2] && waited_for[2]==0 -> current = 2; poll(current);
      :: connect[_pid].to[3] && waited_for[3]==0 -> current = 3; poll(current);
      :: connect[_pid].to[4] && waited_for[4]==0 -> current = 4; poll(current);
      :: connect[_pid].to[5] && waited_for[5]==0 -> current = 5; poll(current);
      :: connect[_pid].to[6] && waited_for[6]==0 -> current = 6; poll(current);
      :: connect[_pid].to[7] && waited_for[7]==0 -> current = 7; poll(current);
      :: else ->
	 if
	   :: counter==adj[_pid] ->
	      no_of_requests = counter;
	      counter = 0;
	      goto child_handshake
	   :: counter==(adj[_pid]-1) ->
	      no_of_requests = counter;
	      counter = 0;
	      find_remaining(_pid,remaining_partner);
	      goto child_handshake
	   :: counter<(adj[_pid]-1) -> goto wait_for_request
	 fi
    od
  };
 
 
child_handshake:
 atomic {
   converter(_pid,child[counter],self_in,self_out);
   self_out!be_my_child;
   self_in=nullchan;
   self_out=nullchan;
   counter++;
   if
     :: (counter==no_of_requests)->
	counter=0;
	if
	  :: no_of_requests==(adj[_pid]-1)->
	     converter(_pid,remaining_partner,self_in,self_out);
	     self_out!be_my_parent;
	     self_in=nullchan;
	     self_out=nullchan;
	     goto wait_for_acks
	  :: else->
	     goto wait_for_acks
	fi
     :: else->
	goto child_handshake
   fi
 };
		
wait_for_acks:
 atomic {
   converter(_pid,child[counter],self_in,self_out);
   self_in?message;
   assert(message==ack);
   message=nullmessage;
   self_in=nullchan;
   self_out=nullchan;
   counter++;
   if
     :: (counter==no_of_requests) ->
	counter=0;
	goto become_parent
     :: else->
	goto wait_for_acks
   fi
 };

become_parent:
 atomic{
   assert(counter==0);
   if
     :: (no_of_requests==adj[_pid]) ->
	elected=_pid;
	goto finish
     :: else->
	converter(_pid,remaining_partner,self_in,self_out);
	partnerid=remaining_partner;
	remaining_partner=0;
	goto response
   fi
 };

finish:
 atomic{
   assert((message==nullmessage)&&(counter==0)&&(partnerid==0)&&(self_in==nullchan)&&(self_out==nullchan))
 }

}

init {
  atomic {

connect[1].to[2]=true; 
connect[2].to[1]=true; 
connect[1].to[3]=true; 
connect[3].to[1]=true; 
connect[2].to[4]=true; 
connect[4].to[2]=true; 
connect[2].to[5]=true; 
connect[5].to[2]=true; 
connect[3].to[6]=true; 
connect[6].to[3]=true; 
connect[3].to[7]=true; 
connect[7].to[3]=true; 


/*set neighbours array */


adj[1]=2; 
adj[2]=3; 
adj[3]=3; 
adj[4]=1; 
adj[5]=1; 
adj[6]=1; 
adj[7]=1; 



run node();
run node();
run node();
run node();
run node();
run node();
run node();
  }
}
