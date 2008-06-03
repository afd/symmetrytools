active proctype foo ()
{ byte x;
  do
  :: x=x
  od
}
never {
do
:: true -> break
od;
accept: assert(0)
}

