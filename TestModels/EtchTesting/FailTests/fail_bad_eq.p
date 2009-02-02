

proctype P(chan c, d)
{

int x;

   c ! d, d;

   d ! c, c, c;

   
x == c;

}