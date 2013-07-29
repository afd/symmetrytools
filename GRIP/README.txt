Compiling GRIP from source
==========================

Prerequisites:
* Java Development Kit (Java 6 or newer should suffice)
* make

- Download SableCC version 3.6 from the SableCC web page:
  http://sablecc.org

- Navigate to symmetrytools/GRIP

- Run SableCC to generate the parser for the symmetric PRISM language:
  java -jar <path-to-sablecc>/lib/sablecc.jar sp.grammar

- Run make to create a jar file for GRIP:
  make jars

Running GRIP on an example
==========================

- Navigate to symmetrytools/GRIP/Examples

- Run GRIP on byzantine8.forgrip.nm:
  java -jar ../GRIP.jar byzantine8.forgrip.nm byzantine8.reduced.nm

- The reduced file will be produced in byzantine8.reduced.nm
