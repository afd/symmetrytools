bit x,y;
active proctype test()
{ 
  do
  :: x=!x
  :: y=!y
  :: x=x /* Comment this out as instructed */
  od
}
never
{ do
  :: skip
  :: x&!y -> break
  od;
  accept: x&!y -> goto accept
}
