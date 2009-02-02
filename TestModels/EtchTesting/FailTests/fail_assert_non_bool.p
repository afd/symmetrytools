

chan c = [1] of {chan};

init {


     c ! c;

     assert (c);

     }
