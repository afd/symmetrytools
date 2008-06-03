mtype={nullmessage,be_my_parent,be_my_child,ack,ack_b};

byte adj[4]

typedef array {
  bool to[4]
};

hidden array connect[4];

hidden pid other_id;

hidden byte dealt_with[4];

byte toss[4]=0;

chan null=[0] of {mtype};

chan onetwo=[1] of {mtype}; 

chan twoone=[1] of {mtype}; 

chan onethree=[1] of {mtype}; 

chan threeone=[1] of {mtype}

inline converter(id1,id2,chanin,chanout) {
/* takes a pair of ids and finds the corresponding in and out channels */ 
  if
    :: (id1==1)->assert((id2==2)||(id2==3));
       if
	 ::(id2==2)->chanin=twoone;chanout=onetwo
	 ::(id2==3)->chanin=threeone;chanout=onethree
       fi
    :: (id1==2)-> assert((id2==1));
		  chanin=onetwo;chanout=twoone
    :: (id1==3)-> assert((id2==1));
		  chanin=onethree;chanout=threeone
  fi
}

inline find_remaining(id1,id2) {
/*takes an id and returns partner that is not a child*/
  if :: connect[id1].to[1] && (!(child[0]==1 || child[1]==1 || child[2]==1 || child[3]==1))->id2=1
     :: connect[id1].to[2] && (!(child[0]==2 || child[1]==2 || child[2]==2 || child[3]==2))->id2=2
     :: connect[id1].to[3] && (!(child[0]==3 || child[1]==3 || child[2]==3 || child[3]==3))->id2=3
  fi
}

inline reset_dealt_with() {
  do
    :: dealt_with[1]!=0->dealt_with[1]=0
    :: dealt_with[2]!=0->dealt_with[2]=0
    :: dealt_with[3]!=0->dealt_with[3]=0
    :: else->break
  od
}

inline check_for_incoming_message(id) {
  assert(_pid!=id);
  converter(_pid,id,self_in,self_out);
  if
    :: full(self_in)->
       child[counter1]=id;
       counter1++
    :: empty(self_in)->skip
  fi;
  self_in=null;
  self_out=null;
  dealt_with[id]=true;
}

proctype node() {

  mtype message=nullmessage;
  pid child[4]=0;
  pid remaining_partner=0;
  byte counter=0;
  byte counter1=0;
  byte no_of_requests=0;
  chan self_in=null;
  chan self_out=null;

  assert(!connect[_pid].to[_pid]);
  
start:
  atomic {
    assert((message==nullmessage)&&(remaining_partner==0)&&(self_in==null)&&(self_out==null)&&(counter==0)&&(counter1==0));

    reset_dealt_with();
    do
      :: connect[_pid].to[1] && dealt_with[1]==0->
	 other_id=1;
	 check_for_incoming_message(other_id)
      :: connect[_pid].to[2] && dealt_with[2]==0->
	 other_id=2; check_for_incoming_message(other_id)
      :: connect[_pid].to[3] && dealt_with[3]==0->
	 other_id=3;
	 check_for_incoming_message(other_id)
      :: else->break;
    od;

    counter=0;
    if
      :: (counter1>=adj[_pid]-1)->
	 no_of_requests=counter1;
	 counter1=0;
	 do
	   :: counter==no_of_requests->break
	   :: counter<no_of_requests->
	      converter(_pid,child[counter],self_in,self_out);
	      self_in?message;
	      assert(message==be_my_parent);
	      message=nullmessage;
	      self_in=null;
	      self_out=null;
	      counter++
	 od;
	 counter=0;
	 if
	   :: (no_of_requests==adj[_pid]-1)->
	      find_remaining(_pid,remaining_partner);
	   :: else->skip
	 fi;
	 goto child_handshake
      :: else->
	 do
	   :: (counter==counter1)->break
	   :: counter<counter1->
	      child[counter]=0;
	      counter++
	 od;
	 counter=0;
	 counter1=0;
	 goto start
    fi
  };
  
response:
  atomic {
    full(self_in);
    assert((message==nullmessage)&&(counter==0));
    self_in?message;
    if
      :: message==be_my_child->
	 message=nullmessage;
	 remaining_partner=0;
	 goto become_child
      :: message==be_my_parent->
	 message=nullmessage;
	 goto contention
    fi
  };
  
become_child:
  atomic {
    empty(self_out);
    self_out!ack;
    assert((message==nullmessage)&&(counter==0)&&(remaining_partner==0));
    self_in=null;
    self_out=null;

    counter=0;
    do
      :: (counter==4)->break
      :: else->child[counter]=0;
	       counter++
    od;
    remaining_partner=0;
    no_of_requests=0;
    counter=0;
    goto finish
  };

contention:
  atomic {
    assert((message==nullmessage)&&(counter==0)&&(remaining_partner!=0));
    if
      :: (toss[_pid]==0 && toss[remaining_partner]==0)->
	 toss[_pid]++;
	 toss[remaining_partner]++;
	 goto winner
      :: else->
	 assert(toss[_pid]==1 && toss[remaining_partner]==1);
	 toss[_pid]=0;
	 toss[remaining_partner]=0;
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
    counter=0;
    do
      ::(counter==4)->break
      ::else->child[counter]=0;counter++
    od;
    counter=0;
    child[0]=remaining_partner;
    remaining_partner=0;
    self_in=null;
    self_out=null;
    goto child_handshake
  };
  
child_handshake:
  atomic {
    if
      :: (no_of_requests==0)->
	 converter(_pid,remaining_partner,self_in,self_out);
	 self_out!be_my_parent;
	 self_in=null;
	 self_out=null;
	 counter=0;counter1=0;
	 goto parent_handshake
      :: else->
loop:	 
	 converter(_pid,child[counter],self_in,self_out);
	 self_out!be_my_child;
	 self_in=null;
	 self_out=null;
	 counter++;
	 if
	   :: (counter==no_of_requests)->
	      counter=0;
	      counter1=0;
	      if
		:: no_of_requests==(adj[_pid]-1)->
		   converter(_pid,remaining_partner,self_in,self_out);
		   self_out!be_my_parent;
		   self_in=null;
		   self_out=null;
		   goto parent_handshake
		:: else->goto parent_handshake
	      fi
	   :: else->goto loop
	 fi
    fi
  };
  
parent_handshake:
  atomic{
    assert((counter==0)&&(counter1==0));
    if
      :: (no_of_requests==0)->
	 goto handshakes_complete
      :: else->
loop2:		     
	 if
	   :: (counter==no_of_requests)->skip
	   :: else->
	      converter(_pid,child[counter],self_in,self_out);
	      if
		:: empty(self_in)->skip
		:: full(self_in)->counter1++
	      fi;
	      counter++;
	      self_in=null;
	      self_out=null;
	      goto loop2
	 fi;
	 assert(counter==no_of_requests);
	 counter=0;
	 if
	   :: counter1<no_of_requests->
	      counter1=0;
	      goto parent_handshake
	   :: else->counter1=0;
	      do
		::(counter==no_of_requests)->break
		::else->converter(_pid,child[counter],self_in,self_out);
			assert(full(self_in));
			self_in?message; assert(message==ack);
			message=nullmessage;
			self_in=null;self_out=null;counter++
		   od;
		   assert(counter==no_of_requests);counter=0;
	 fi
    fi
  };

handshakes_complete:
  atomic {
    assert(counter==0);
    if
      :: (no_of_requests==adj[_pid])->
	 counter=0;
	 do
	   :: (counter==4)->break
	   :: else->child[counter]=0;
		    counter++
	 od;
	 remaining_partner=0;
	 no_of_requests=0;
	 counter=0;
	 goto finish
      :: else->
	 converter(_pid,remaining_partner,self_in,self_out);
	 goto response
    fi
  };
	
finish:
  atomic {
    assert((message==nullmessage)&&(counter==0)&&(remaining_partner==0)&&(self_in==null)&&(self_out==null))
  }
}

init {

  atomic {

    connect[1].to[2]=true;
    connect[2].to[1]=true;
    connect[1].to[3]=true;
    connect[3].to[1]=true;

    adj[1]=2;
    adj[2]=1;
    adj[3]=1;

    run node();
    run node();
    run node();

  }

}
