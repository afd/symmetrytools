# Makefile
# Project maintenance for saucy
#
# by Paul T. Darga <pdarga@umich.edu>
# and Mark Liffiton <liffiton@umich.edu>
#
# Copyright (C) 2004, The Regents of the University of Michigan
# See the LICENSE file for details.

# .POSIX :

# POSIX doesn't define the nature of -O optimizations on the compiler, so
# these have to be set by the site.  Here is an example setting for gcc:

CC=gcc
CFLAGS=-ansi -pedantic -Wall -O3

# The objects we depend on
OBJECTS=main.o saucy.o saucyio.o

saucy : $(OBJECTS)
	$(CC) $(LDFLAGS) -o $@ $(OBJECTS)

# Header dependencies
main.o saucy.o saucyio.o : saucy.h

# Useful fake target
clean : ; rm -f saucy *.o
