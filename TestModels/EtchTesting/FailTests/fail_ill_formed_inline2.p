

inline sum(result, x, y )
{
    result = x + y;
}


inline avg(res, a, b, c, d)
{
{
int temp;
sum(res, a, b);
sum (temp, c, d);
sum(res, res, temp);
res = res / 4;
}

}



init {

     int a, b, c;
     chan d;
     a = 1; b = 2; c = 3;

     int result;


     avg(result, a, b, c, d);


     }