

init {

     bool b;

     chan c;

     c ! c, 2;

     b = (( 5 > 2 -> 3 : 4) + c) > 2;


     }