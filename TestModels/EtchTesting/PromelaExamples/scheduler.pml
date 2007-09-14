/* Modification of http://www.cs.sun.ac.za/~pja/modelchecking1/gneiss.mdl */

#define QUEUE 3
#define null 0

mtype = { enter, resume, call, select, start, interrupt, process, ready, complete }

chan toclient = [0] of { byte, byte }
chan toscheduler = [0] of { byte, byte }
chan tocontroller = [0] of { byte, byte }
chan todriver = [0] of { byte, byte }
chan todevice = [0] of { byte }

proctype client(byte id)
{
   toscheduler ! enter(id);
   do
   :: true ->
         if
         :: id == 1 -> 
               toclient ? resume(1) /* from controller */
         :: id == 2 -> 
               toclient ? resume(2) /* from controller */
         :: id == 3 -> 
               toclient ? resume(3) /* from controller */
         fi;
         tocontroller ! call(id)
   od
}

active proctype scheduler()
{
   byte p;
   chan queue = [QUEUE] of {byte};

   do
   :: true ->
      if
      :: toscheduler ? enter(p) -> /* from client or driver */
         if
	 :: p != null -> queue ! p
	 :: p == null -> skip
	 fi
      :: toscheduler ? select(p) -> /* from controller */
         if
	 :: nempty(queue) -> queue ? p; tocontroller ! process(p)
         :: empty(queue) -> tocontroller ! process(null)
	 fi
      fi
   od
}

active proctype controller()
{
   byte p;

   do
   :: true ->
      if
      :: toscheduler ! select(p) ->
            tocontroller ? process(p); /* from scheduler */
	    if
	    :: p != null -> 
                  toclient ! resume(p)
	    :: p == null -> 
                  skip
	 fi
      :: tocontroller ? call(p) -> /* from client */
            todriver ! ready(p)
      :: tocontroller ? interrupt(0) -> /* from device */
            todriver ! complete(0)
      fi
   od
}

active proctype driver()
{
   byte current, id;
   bool idle = true;
   chan queue = [QUEUE] of {byte}

   do
   :: true ->
      if
      :: todriver ? ready(id) -> /* from controller */
         if
	 :: idle -> 
               current = id;
	       todevice ! start;
	       idle = false
         :: !idle -> 
               queue ! id
	 fi
      :: todriver ? complete(0) -> /* from controller */
            toscheduler ! enter(current);
	    if
	    :: empty(queue) -> 
                  idle = true
	    :: nempty(queue) ->
	          queue ? current; todevice ! start
	    fi
      fi
   od
}

active proctype device()
{
   do
   :: true ->
         todevice ? start; /* from driver */
         tocontroller ! interrupt(0)
   od
}

init 
{
   atomic 
   {
      run client(1);
      run client(2);
      run client(3)
   }
}
