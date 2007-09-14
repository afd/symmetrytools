mtype = {hold}

proctype Agent(chan listen, talk)
{
   talk!listen(hold);	
   talk!hold(listen);
}
