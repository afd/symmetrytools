chan null = [1] of {chan,bit}; 
chan silly = [0] of {chan,bit};
chan partner

proctype User (byte selfid; chan self) 
{
   chan messchan = null; 
   partner!silly,self;
   self?messchan,1; 
   self!partner,0;
}

