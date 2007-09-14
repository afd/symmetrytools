proctype User (byte selfid) 
{
   chan one = [1] of {chan,chan};
   chan two = [1] of {chan,chan,chan};

   one!one,one;
   one?two,two;

}

