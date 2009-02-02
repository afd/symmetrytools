

inline max(a,b,result) {
  if
    :: a<b -> result = b
    :: else -> result = true
  fi
}

inline thirdIsMax(list,result) {
  mtype list0 = list[0];
  mtype list1 = list[1];
  mtype list2 = list[2];
  max(list0,list1,temp);
  if :: temp==list[2] ->
	max(list1,list2,temp);
	if :: temp==list[2] ->
	      result = true
	   :: else ->
	      result = 5
	fi;
     :: else -> result = false
  fi;
}

active proctype A() {
  mtype things[3];
  mtype result;
  bool thirdIsMax;
  thirdIsMax(things,result);  
}
