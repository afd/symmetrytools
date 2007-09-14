mtype = { msg };

chan A = [1] of {mtype};

init {

     A!4;
     A?msg;
     }