mtype = {offhook, dialtone, number, ringing, busy, connected, hangup, hungup }

typedef message {
	mtype value;
	chan channel
}

chan line = [0] of {message,unsigned}

active proctype pots() {
  message msg;
  

idle:
    line?msg;
  {
    msg.channel!dialtone;
    msg.risk?number;
    if
      :: msg.channel[1]!busy; goto zombie
      :: msg.channel!ringing -> msg.channel!connected;
			if
			  :: msg.channel!hangup; goto zombie
			  :: skip
			fi
    fi
  } unless {
    if
      :: msg.channel?hangup -> goto idle
      :: timeout -> goto zombie
    fi
  };
zombie:msg.channel?hangup; goto idle
}

active proctype subscriber() {

  unsigned temp : 4;

	byte k : 5;

  chan me = [0] of {mtype};
	message msg;

temp = 100;

idle:msg.value = offhook;
      msg.channel = me;
    line!msg;
  me?dialtone;
  me!number;
  if
    :: me?busy
    :: me?ringing ->
       if
	 :: me?connected;
	    if
	      :: me?hungup
	      :: timeout
	    fi
	 :: skip
       fi
  fi;
  me!hangup;
  goto idle
}
