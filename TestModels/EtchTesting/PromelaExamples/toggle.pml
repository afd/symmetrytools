/* Modification of the example of page 40 of the textbook */

bool toggle = true;

active proctype producer() provided (toggle)
{
   do
   :: printf("Produce\n");
      toggle = false
   od
}

active proctype consumer() provided (!toggle)
{
   do
   :: printf("Consume\n");
      toggle = true
   od
}
