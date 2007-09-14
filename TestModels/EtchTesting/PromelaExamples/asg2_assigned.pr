bit x,y;
active proctype test1()
{ 
  do
  :: x=x
  :: x=!x
  od
}
active proctype test2()
{ 
  do
  :: y=y
  :: y=!y
  od
}
never
{ do
  :: skip
  :: x -> break
  od;
  accept: y -> goto accept
}


    