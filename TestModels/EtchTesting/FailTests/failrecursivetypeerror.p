chan null = [1] of {chan,bit}; 
chan partner

proctype User (byte selfid) 
{
   chan self = [1] of {chan,bit};
   chan messchan = null; 
   self!self,1;
   self!partner,0;
   partner!self,1;
   self?messchan,messchan; 
   self!partner,0;
}

