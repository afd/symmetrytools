Etch 1.0 - usage notes
======================

Etch is an Enhanced Type CHecker for Promela, developed by Alastair F. Donaldson and Simon J. Gay.  Etch uses type inference to catch problems statically which SPIN misses until vefification (or in some cases completely).  Etch was introduced via a tool demonstration at SPIN 2005.

As usual, Etch comes with no warranty - it is a research prototype and you use it at your own discretion.

Requirements
------------

Java(TM) 2 Runtime Environment, Standard Edition, version 1.5.0_16 or later.

Running Etch
------------

java -jar Etch.jar model.p

where 'model.p' is the name of the Promela file you wish to check.  Etch will report any type errors it finds, otherwise it will show you reconstructed types for the model.

Additional options
------------------

To display all options:
   java -jar Etch.jar help

For help on a specific option:
   java -jar Etch.jar help <option name>


-channelredundancy:

   java -jar Etch.jar -channelredundancy model.p

Produces reconstructed types which potentially show smaller types for channels.  E.g. in this example:

chan A = [1] of {int}

active proctype P()
{
	byte x;
	A!4; 
	A?x;
}

Etch will report that A could have been declared with field type {byte}, which would be more efficient.


-strictarrayindexing

   java -jar Etch.jar -strictarrayindexing model.p

With this option Etch will report errors if an array is indexed with type short or byte (by default this will not be flagged up as an error).


-strictassignment

   java -jar Etch.jar -strictassignment model.p

With this option Etch will report errors if a variable is assigned an expression of too large a type, e.g. if a byte variable is assigned an int variable's value (by default this will not be flagged up as an error).


-cpp <path to cpp utility>

   java -jar Etch.jar -cpp <path to cpp utility> model.p

Etch requires the C preprocessor, cpp.  If you are using Cygwin under Windows, then cpp.exe may be a symbolic link.  If this is the case then you need to run Etch with the option: -cpp <link target>, where <link target> is the target for the symbolic link, given in Windows form.  So, for example, if cpp.exe is a link to /etc/alternatives/cpp.exe, you should use the option -cpp C:\\cygwin\\etc\\alternatives\\cpp.exe.  This is a limitation of Etch which the designers hope to fix in a future release.



Source code
-----------

You can check out the source code for Etch as follows:

svn co svn://edison.comlab.ox.ac.uk/symmetrytools/trunk TopSPIN

This checks out the complete TopSPIN symmetry reduction package, of which Etch is a component.  Look in src/etch for the Etch source code.

Acknowledgement
---------------

Etch is based on a Promela parser generated using SableCC (sablecc.org).
