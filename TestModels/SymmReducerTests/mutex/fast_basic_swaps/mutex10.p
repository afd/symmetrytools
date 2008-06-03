mtype = {N,T,C}
mtype st[11]=N

proctype user() {
  do
    :: d_step { st[_pid]==N -> st[_pid]=T }
    :: d_step { st[_pid]==T &&
        (st[1]!=C && st[2]!=C && st[3]!=C && st[4]!=C && st[5]!=C && st[6]!=C && st[7]!=C && st[8]!=C && st[9]!=C && st[10]!=C)
	-> st[_pid]=C
       }
    :: d_step { st[_pid]==C -> st[_pid]=N }
  od
}

init {
  atomic {
    run user();
    run user();
    run user();
    run user();
    run user();
    run user();
    run user();
    run user();
    run user();
    run user();
  }
}
