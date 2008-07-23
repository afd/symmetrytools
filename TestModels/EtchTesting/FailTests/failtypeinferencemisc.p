

chan A = [1] of {short};

chan B = [1] of {bool};

init {

     chan C = [3] of {chan};

C!A;

C!B;



     }