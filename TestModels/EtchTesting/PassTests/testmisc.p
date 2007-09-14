mtype = {hello,goodbye,hiya};
chan link = [1] of {chan,chan,mtype,byte,int};
chan first = [1] of {byte};
chan second = [1] of {byte}

proctype A(byte x; chan a, b) {
	a++;
	x--;
	link!a,b,hello,x,12;
}

proctype B() {
	chan a;
	chan b;
	link?b,a,hello,5,12;

}

init {
	run B();
	run A(6, first, second)
}