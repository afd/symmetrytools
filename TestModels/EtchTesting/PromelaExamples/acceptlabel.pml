/* Variation on example on page 81 of textbook */

byte x = 2;

active proctype A()
{
   do
   :: x = 3 - x; accept : skip
   od
}

/*
  spin -a acceptlabel
  cc -o pan pan.c
  pan -a
*/
