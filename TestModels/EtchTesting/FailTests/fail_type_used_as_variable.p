


typedef T
{
   chan D = [1] of {chan, chan, chan, chan};
}

chan E = [1] of {chan, chan};

chan C = [1] of {chan};

chan B = [1] of {int, chan};

init {

     T myT;

     T.D!T.D,E,C,B;

     E!T.D,E;

     C!C;

     B!5,B;


     D.x = 5;


     }