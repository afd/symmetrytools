


chan A = [1] of {short}

chan B = [1] of {short}

chan C = [1] of {chan}


chan D = [200] of {int}

chan E = [100] of {int}

chan F = [30] of {chan}

init {

     short s;

     int i;
     
     C!A;

     C?B;

     B!s;

     F!D;

     F?E;

     E!i
     
     }
