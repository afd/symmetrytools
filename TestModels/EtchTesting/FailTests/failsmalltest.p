chan null = [1] of {chan,bit}; 
chan partner

proctype User (byte selfid) 
{
   chan one = [1] of {chan,chan};
   chan two = [1] of {chan,chan};
   chan three = [1] of {chan,chan};
   chan four = [1] of {chan,chan};

chan five = [1] of {bit};

chan temp;

one!two,three;
two!three,four;
three!four,one;
four!one,two;
one?four,three;
two?one,four;
three?two,one;
four?three,two;

one!five,five;

one?temp,temp;

temp?0;

one?two,two;

two?0,0;

//five!0;

/*chan messchan = null; 
   self!self,1;
   self!partner,0;
partner!self,1;
   self?messchan,messchan; 
   self!partner,0;*/
}

