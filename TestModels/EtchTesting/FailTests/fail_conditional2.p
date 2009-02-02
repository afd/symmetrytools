chan c = [1] of {int};

chan d;

init {

     
     int x;

     int y;

     d ! d, c, c, d, c, c, d, d;

     x = ( d -> ( false -> 5 : 6) : ( d == d -> x : y ) );

     }

