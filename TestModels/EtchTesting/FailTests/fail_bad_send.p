

chan x = [1] of {chan};


init {
     chan c;

     chan d;
     c!c;

     x!c;

     x?d;

     d!5;


     }