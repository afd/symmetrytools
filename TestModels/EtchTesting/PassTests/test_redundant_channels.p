chan A;
chan B;
chan C;
chan D;

proctype P()
{
A!4;
B!3;
}

proctype Q()
{
byte x;
A?x;
C?x;
}

init {
     run P();
     run Q();
     }
