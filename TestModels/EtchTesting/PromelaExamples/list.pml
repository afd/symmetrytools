typedef Node
{
   int value;
   int next
}

Node list[10]

proctype print()
{
  int i = 0;
   do
   :: (i == -1) -> break
   :: (i != -1) ->
         printf("%d\n", list[i].value);
         i = list[i].next
   od;
}

active [1] proctype create()
{
   int i = 0;
   do
   :: (i < 10) ->
         list[i].value = i;
         list[i].next = i + 1;
         i++
   :: (i == 10) -> 
         list[9].next = -1;
         break
   od;
   run print()
}
