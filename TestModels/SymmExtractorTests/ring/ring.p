chan one_two = [1] of {byte,pid};
chan two_three = [1] of {byte,pid};
chan three_one = [1] of {byte,pid};
chan guid_server = [3] of {byte}

proctype user(chan in, out) {
  byte id;
  pid current_pid;
  byte current_byte;
  pid leader;
  
  guid_server?id;

  out!id,_pid;
end:
  do
    :: in?current_byte,current_pid;
       if
	 :: current_byte == 0 -> leader = current_pid; out!current_byte,current_pid
	 :: else ->
	    if
	      :: id < current_byte -> out!current_byte,current_pid
	      :: current_byte < id -> skip
	      :: current_byte == id -> leader = _pid; out!0,_pid; in?0,_pid
				       
	    fi
       fi
  od
}

proctype guidserver() {
  guid_server!1;
  guid_server!2;
  guid_server!3;
}

init {
  atomic {
    run user(three_one,one_two);
    run guidserver();
    run user(one_two,two_three);
    run user(two_three,three_one)
  }
}
