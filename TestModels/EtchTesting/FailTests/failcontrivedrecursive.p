chan A = [1] of {chan};
chan B = [1] of {chan};
chan C = [1] of {chan};
chan D = [1] of {chan,chan,chan};
chan E = [1] of {chan,chan,chan};
chan F = [1] of {byte}

init {
  A!B;
  B!C;
  C!A;
  D!E,E,A;
  E!D,E,B;
  F!E
}
