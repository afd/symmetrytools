typedef myStructInner
{
int w, z;
}


typedef myStruct
{
myStructInner in;
int y;
}

myStruct s;

init {

     s.in.w;

}
