chan c = [1] of {int};

chan d;

init {

     d = c;

     int x;

     int y;

     x = ( 5 < ( x >= y -> 17 : x+y ) -> ( false -> 5 : 6) : ( c == d -> x : y ) );

     }

