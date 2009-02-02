

inline first(x)
{
x++;
}

inline second(x)
{
x--;
}

inline doIt(mac, x)
{
mac(x);
}


init {
     int y;

     /* You can't pass an inline name as an inline parameter.  Phew!! */
     doIt(first, y);

     }
