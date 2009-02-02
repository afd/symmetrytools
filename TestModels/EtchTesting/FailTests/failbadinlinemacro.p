inline f(a,b)
{
a = 4;
b = 7;

}

inline g(x,y)
{

x = 3;
y = true;
f(x,y);

}

inline h(a,b)
{
a = 1;
b = false;

g(a,b);

}

init {
     int x;
     bool y;

     h(x,y);


     }
