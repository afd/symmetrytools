

chan c = [1] of {chan, chan};

init {

     int x [ 10 ] ;


     c ! c , c;

     x[c] = 12;

     }
