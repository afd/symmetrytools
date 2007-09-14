


chan A = [0] of {chan};
chan B = [0] of {chan};
chan C = [0] of {chan};

chan D = [0] of {chan,chan,chan};
chan E = [0] of {chan,chan,chan};

chan F = [0] of {byte}

init {
     A!B;
     B!C;
     C!A;

     D!E,E,A;
     E!D,E,B;

     F!E
     }