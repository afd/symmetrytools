chan null = [1] of {chan,bit}; 
chan partner

proctype User (byte selfid) 
{
   chan self = [1] of {chan,bit};
   chan messchan = null; 
   partner!silly,self;
   self?messchan,messchan; 
   self!partner,0;
}

