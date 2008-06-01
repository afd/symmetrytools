typedef Mail {
  pid sender;        
  pid receiver;
  byte key;
  bit body
};
   
chan null = [1] of {Mail};
chan zero = [1] of {Mail};
chan one = [1] of {Mail};
chan network = [2] of {Mail}

inline mailbox_lookup(login,box,myerror) {
  if
    :: (login==1) -> box = one
    :: (login==2) -> box = two
    :: else -> myerror = 1
  fi
}

proctype Client() {
  chan mybox=null;
  bit is_error=0;
  Mail msg;

  atomic {
    msg.sender=0;
    msg.receiver=0;
    msg.key=0;
    msg.body=0;
      
    mailbox_lookup(_pid,mybox,is_error)
	 };

initial:
  atomic {
    (nempty(mybox)||nfull(network));
    if :: nempty(mybox) -> goto delivermail
       :: empty(mybox) && nfull(network) ->  goto sendmail                                             
    fi;
      
delivermail:
    mybox?msg;
    goto endClient;  
    
sendmail:
    
    if
      :: msg.receiver= 1
      :: msg.receiver= 2
    fi;

    msg.sender = _pid;
    network!msg;
    
endClient:
    msg.sender = 0; 
    msg.receiver = 0;
    msg.body = 0;
    msg.key = 0;
            
    goto initial 

  }
}

proctype Network_Mailer() {
  Mail msg;
  chan deliverbox=null;
  bit is_error=0;
  
  atomic {
    msg.sender = 0; 
    msg.receiver= 0; 
    msg.key=0;
    msg.body=0;
  };

loop:
  atomic {
    network?msg;
    mailbox_lookup(msg.receiver,deliverbox,is_error);
    if
      ::is_error==1->is_error=0;
		     msg.receiver=0;
		     msg.sender=0;
		     msg.key=0;
		     msg.body=0;
		     goto loop
      ::else->skip
    fi
  };

deliver:
  atomic {
    deliverbox!msg;
    msg.sender = 0; 
    msg.receiver= 0;
    msg.body = 0; msg.key = 0;
    deliverbox = null;   
    goto loop
  }
}
		
init {
  atomic {
    run Network_Mailer();
    run Client();
    run Client();
  }
}
