/* Variation on example on page 81 of textbook */

byte x = 2;

active proctype A()
{
   progress :
   do
   :: x = 3 - x
   od
}

/*
  spin -a progresslabel.pml
  cc -o pan -DNP pan.c
  pan -l
*/
