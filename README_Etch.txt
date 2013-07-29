To build Etch from source
=========================

Prerequisites:
* Java Development Kit (Java 6 or newer should suffice)
* perl
* make

- Download SableCC version 3.6 from the SableCC web page:
  http://sablecc.org

- Navigate to symmetrytools

- Run SableCC to generate the parser for Promela:
  java -jar <path-to-sablecc>/lib/sablecc.jar promela.grammar

- Run a PERL script to apply a small fix:
  perl apply_patch.pl

- Run the Etch makefile:
  make -f EtchMakefile jars

- This will create Etch.jar

Running Etch on an example
==========================

- Naviage to symmetrytools/TestModels/EtchTesting/FailTests

- Run Etch on, e.g., failchanoponchannel1.p:
  java -jar ../../../Etch.jar failchanoponnonchannel1.p

- You should get an error message along the lines of:

  Error at "failchanoponnonchannel1.p", line 8:
     The "nempty" operator can only be applied a channel variable; 
     here it has been applied to a variable of type "array(size 5)
     of chan X0".
