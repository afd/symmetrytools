#!/usr/local/bin/perl
#
# Script to prepare a Promela model for symmetry reduction to be applied.
# Uses SPIN to generate "pan" files for the model, copies these "pan" files
# into "sympan" files, and adjusts the "sympan" files to be ready for
# symmetry reduction.  The script also copies "c" files to represent
# permutation groups into the current directory, adjusts "group.h" to
# indicate the number of processes, channels and generators, and compiles
# "group.c".

################
# Declarations #
################

$symmpath = $ARGV[7];  # This is where templates are held.

$model = $ARGV[0];                    # The Promela model is taken as the first command line argument

$groupGenerators = $ARGV[8];

# Remove whitespace from the start and end of the string
sub trimwhitespace($)
{
	my $string = shift;
	$string =~ s/^\s+//;
	$string =~ s/\s+$//;
	return $string;
}

# Convert a GAP permutation into a permutation for SPIN
sub convertPerm($)
{
    $perm = $_[0];
    while($perm =~ /,/) {
	$perm =~ s/,/ /;
    }

    return $perm;

    return $result;
}

sub compare($$)
{
    if($segment) {
	return "lt($_[0],$_[1])";
    } else {
	return "memcmp($_[0],$_[1],vsize)<0";
    }
}

#############
# Algorithm #
#############

$useTranspositions = ($ARGV[4] eq "true");

$useStabiliserChain = ($ARGV[5] eq "true");

$segment = ($ARGV[6] eq "SEGMENT");

$flatten = ($ARGV[6] eq "FLATTEN");

$markers = (($ARGV[6] eq "EXACTMARKERS")||($ARGV[6] eq "APPROXMARKERS")||($ARGV[6] eq "BOSNACKIMARKERS"));

my $markerstype;
if($markers) {
    $markerstype = $ARGV[6];
}

system("spin","-a","$model");                         # Generate pan files.

for($counter=0; $counter<5; $counter++) {             # Copy pan files into
    $ending = ("c","h","b","t","m")[$counter];        # sympan files.
    system("cp","pan.$ending","sympan.$ending");
}

if((!$markers) && $useTranspositions) {
    system("cp","$symmpath/groupTranspositions.c","./group.c");                 # Copy group theory files into current
    system("cp","$symmpath/groupTranspositions.h","./group.h");                 # directory.
} elsif(!$markers && !$useTranspositions) {
    system("cp","$symmpath/groupBasic.c","./group.c");                 # Copy group theory files into current
    system("cp","$symmpath/groupBasic.h","./group.h");                 # directory.
}



# DEAL WITH sympan.h

open(MODEL, "sympan.h");                              # Read in "sympan.h".
@lines = <MODEL>;
close(MODEL);

open(MODEL, ">sympan.h");                                # Look through lines of "sympan.h".
for($counter=0; $counter<scalar(@lines); $counter++) {
    $lines[$counter] =~ s/pan\./sympan\./;               # Replace "pan." with "sympan.".
    print MODEL "$lines[$counter]";
    if($lines[$counter] =~ /\*\* function prototypes \*\*/) {    # Add prototype for "rep" function.
	print MODEL "State *rep(State *orig_now); /* ADDED FOR SYMMETRY */\n";
    }
}
close(MODEL);

# DEAL WITH sympan.c
open(GROUP_INFO, $ARGV[3]);
@group_info = <GROUP_INFO>;
close(GROUP_INFO);

open(MODEL, "sympan.c");                              # Read in "sympan.c".
@lines = <MODEL>;
close(MODEL);

open(MODEL, ">sympan.c");

for($counter=0; $counter<scalar(@lines); $counter++) {   # Look through lines of "sympan.c".

    if(($lines[$counter] =~ "&now") && ($lines[$counter] =~ "store")) {
	$lines[$counter] =~ s/&now/rep(&now)/;           # If "&now" is being stored, replace "&now" with "rep(&now)".
    }

    $lines[$counter] =~ s/"pan.h"/"sympan.h"/;           # "#include "pan.h"" becomes "#include "sympan.h""
    
    print MODEL "$lines[$counter]";

    if($lines[$counter] =~ /"sympan.h"/) {               # Once the line which includes "sympan.h" has been dealt with,

	print MODEL "/* ADDED FOR SYMMETRY */\n\n";
	if(!$markers) {
	    print MODEL "#include \"group.h\"\n\n";
	}
	print MODEL "State tmp_now, min_now, current_min;\n\n";
	print MODEL "#define SEG(state,pid)    (((uchar *)state)+proc_offset[pid])\n";
	print MODEL "#define QSEG(state,cid)    (((uchar *)state)+q_offset[cid])\n";
	print MODEL "#define VAR(state,pid,var,type)   ((type *)SEG(state,pid))->var\n";
	print MODEL "#define QVAR(state,cid,var,type)   ((type *)QSEG(state,cid))->var\n\n";

	if($useTranspositions && !($markerstype eq "BOSNACKIMARKERS")) {
	    print MODEL "void applyPrSwapToState(State *s, int a, int b) {\n";
	    print MODEL "  /* JAVA */\n\n";
	    print MODEL "}\n\n";

	    if(!$markers) {
		print MODEL "void applyChSwapToState(State *s, int a, int b) {\n";
		print MODEL "  /* JAVA */\n\n";
		print MODEL "}\n\n";

		print MODEL "void applyPermToState(State *s, struct perm *alpha) {\n";
		print MODEL "  int i;\n";
		print MODEL "  for(i=0; i<alpha->prLength; i=i+2) {\n";
		print MODEL "    applyPrSwapToState(s,alpha->pr[i],alpha->pr[i+1]);\n";
		print MODEL "  }\n\n";
		print MODEL "  for(i=0; i<alpha->chLength; i=i+2) {\n";
		print MODEL "    applyChSwapToState(s,alpha->ch[i],alpha->ch[i+1]);\n";
		print MODEL "  }\n\n";
		print MODEL "}\n\n";
	    }

	} elsif(!$markers) {
	    print MODEL "void applyPermToState(State *s, struct perm *alpha) {\n";
	    print MODEL "  int j, slot;\n";
	    print MODEL "  State *temp = (State *)malloc(sizeof(State));\n";
	    print MODEL "  memcpy(temp, s, vsize);\n\n";
	    print MODEL "  /* JAVA */\n\n";
	    print MODEL "  memcpy(s,temp,vsize);\n";
	    print MODEL "  free(temp);\n";
	    print MODEL "}\n\n";
	}

	if($segment) {

	    print MODEL "int lt(State *s, State *t) {\n";
	    print MODEL "  /* JAVA */\n\n";
	    print MODEL "  return 0;\n";
	    print MODEL "}\n\n";

	    print MODEL "  /* EQUAL METHODS */\n\n";

	    print MODEL "void freePerm(struct perm p) {\n";
	    print MODEL "  free(p.pr);\n";
	    print MODEL "  free(p.ch);\n";
	    print MODEL "}\n\n";

	    print MODEL "#define CACHE_SIZE (NO_PROCS+NO_CHANS)*(NO_PROCS+NO_CHANS)\n";
	    print MODEL "int noStabilisers = 0;\n";
	    print MODEL "char* stabiliserKeys[CACHE_SIZE];\n";
	    print MODEL "struct perm*** stabiliserValues[CACHE_SIZE];\n";
	    print MODEL "int stabiliserNoLevels[CACHE_SIZE];\n";
	    print MODEL "int* stabiliserCosetsPerLevel[CACHE_SIZE];\n\n";

	    print MODEL "int isKey(char* s) {\n";
	    print MODEL "  int i;\n";
	    print MODEL "  for(i=0; i<noStabilisers; i++) {\n";
	    print MODEL "    if(strcmp(s,stabiliserKeys[i])==0) {\n";
	    print MODEL "      return i;\n";
	    print MODEL "    }\n";
	    print MODEL "  }\n";
	    print MODEL "  return -1;\n";
	    print MODEL "}\n\n";

	    print MODEL "char* constructPartition(State *s) {\n";
	    print MODEL "  int processClasses[NO_PROCS];\n";
	    print MODEL "  int channelClasses[NO_CHANS];\n";
	    print MODEL "  int noProcessClasses = 0;\n";
	    print MODEL "  int noChannelClasses = 0;\n\n";
	    print MODEL "  int i;\n";
	    print MODEL "  for(i=0; i<NO_PROCS; i++) {\n";
	    print MODEL "    processClasses[i] = -1;\n";
	    print MODEL "  }\n\n";
	    print MODEL "  for(i=0; i<NO_CHANS; i++) {\n";
	    print MODEL "    channelClasses[i] = -1;\n";
	    print MODEL "  }\n\n";
	    print MODEL "  char* result = (char*)malloc(3*(NO_PROCS+NO_CHANS*sizeof(char)));\n";
	    print MODEL "  result[0] = '\\0';\n\n";
	    print MODEL "  char temp[5];\n\n";
	    print MODEL "  strcat(result,\"ptn:\");\n\n";
	    print MODEL "  /* JAVA */\n\n";
	    print MODEL "  strcat(result,\"\");\n\n";
	    print MODEL "  return result;\n";
	    print MODEL "}\n\n";


	    print MODEL "void segment(State *s) {\n\n";
	    print MODEL "  char *partitionString = constructPartition(s);\n\n";
	    print MODEL "  struct perm** traversalChain;\n";
	    print MODEL "  int noLevels;\n";
	    print MODEL "  int* cosetsPerLevel;\n";
	    print MODEL "  int index = isKey(partitionString);\n\n";
	    print MODEL "  if(index!=-1) {\n";
	    print MODEL "    free(partitionString);\n";

	    print MODEL "    if(stabiliserNoLevels[index]==0) {\n";
	    print MODEL "      return;\n";
	    print MODEL "    }\n\n";

	    print MODEL "    traversalChain = stabiliserValues[index];\n";
	    print MODEL "    noLevels = stabiliserNoLevels[index];\n";
	    print MODEL "    cosetsPerLevel = stabiliserCosetsPerLevel[index];\n";
	    print MODEL "  } else {\n";
	    print MODEL "    printf(\"%s\",partitionString);\n";
	    print MODEL "    char line[256];\n";
	    print MODEL "    fgets(line,256,stdin);\n";


	    print MODEL "    if(strncmp(line,\"identity\",8)==0) {\n";
	    print MODEL "      stabiliserKeys[noStabilisers] = partitionString;\n";
	    print MODEL "      stabiliserNoLevels[noStabilisers] = 0;\n";
	    print MODEL "      noStabilisers++;\n";
	    print MODEL "      return;\n";
	    print MODEL "}\n\n";

	    print MODEL "    sscanf(line,\"%d\",&stabiliserNoLevels[noStabilisers]);\n";
	    print MODEL "    stabiliserCosetsPerLevel[noStabilisers] = (int*)malloc(stabiliserNoLevels[noStabilisers]*sizeof(int));\n";
	    print MODEL "    traversalChain = (struct perm**)malloc(stabiliserNoLevels[noStabilisers]*sizeof(struct perm*));\n\n";
	    print MODEL "    int i;\n";
	    print MODEL "    for(i=0; i<stabiliserNoLevels[noStabilisers]; i++) {\n";
	    print MODEL "      fgets(line,256,stdin);\n";
	    print MODEL "      sscanf(line,\"%d\",&stabiliserCosetsPerLevel[noStabilisers][i]);\n";
	    print MODEL "      traversalChain[i] = (struct perm*)malloc(stabiliserCosetsPerLevel[noStabilisers][i]*sizeof(struct perm));\n";
	    print MODEL "      traversalChain[i][0] = constructPerm(\"\");\n";
	    print MODEL "      int j;\n";
	    print MODEL "      for(j=1; j<stabiliserCosetsPerLevel[noStabilisers][i]; j++) {\n";
	    print MODEL " 	 fgets(line,256,stdin);\n";
	    print MODEL " 	 traversalChain[i][j] = constructPerm(line);\n";
	    print MODEL "      }\n";
	    print MODEL "    }\n\n";
	    print MODEL "    stabiliserKeys[noStabilisers] = partitionString;\n";
	    print MODEL "    stabiliserValues[noStabilisers] = traversalChain;\n";
	    print MODEL "    noLevels = stabiliserNoLevels[noStabilisers];\n";
	    print MODEL "    cosetsPerLevel = stabiliserCosetsPerLevel[noStabilisers];\n\n";
	    print MODEL "    noStabilisers++;\n\n";
	    print MODEL "  }\n\n";
	    print MODEL "  // Do minimisation\n";
	    print MODEL "  int levelCounters[noLevels];\n\n";
	    print MODEL "  int i;\n";
	    print MODEL "  for(i=0; i<noLevels; i++) {\n";
	    print MODEL "    levelCounters[i] = 0;\n";
	    print MODEL "  }\n\n";
	    print MODEL "  State partialImages[noLevels];\n";
	    print MODEL "  State original_s;\n";
	    print MODEL "  memcpy(&original_s,s,vsize);\n";
	    print MODEL "  memcpy(&partialImages[noLevels-1],&original_s,vsize);\n";
	    print MODEL "  applyPermToState(&partialImages[noLevels-1],&traversalChain[noLevels-1][0]);\n";
	    print MODEL "  for(i=noLevels-2; i>=0; i--) {\n";
	    print MODEL "    memcpy(&partialImages[i],&partialImages[i+1],vsize);\n";
	    print MODEL "    applyPermToState(&partialImages[i],&traversalChain[i][0]);\n";
	    print MODEL "  }\n\n";
	    print MODEL "  for(;;) {\n";
	    print MODEL "    if(memcmp(&partialImages[0],s,vsize)<0) {\n";
	    print MODEL "      memcpy(s,&partialImages[0],vsize);\n";
	    print MODEL "    }\n";
	    print MODEL "    int finished = true;\n";
	    print MODEL "    for(i=noLevels-1; i>=0; i--) {\n";
	    print MODEL "      if(levelCounters[i]<cosetsPerLevel[i]-1) {\n";
	    print MODEL "	 finished = false;\n";
	    print MODEL "	 break;\n";
	    print MODEL "      }\n";
	    print MODEL "    }\n\n";
	    print MODEL "    if(finished) {\n";
	    print MODEL "      break;\n";
	    print MODEL "    }\n\n";
	    print MODEL "    int levelToUpdate = 0;\n\n";
	    print MODEL "    for(;;) {\n";
	    print MODEL "      if(levelCounters[levelToUpdate]<cosetsPerLevel[levelToUpdate]-1) {\n";
	    print MODEL "	levelCounters[levelToUpdate]++;\n";
	    print MODEL "	for(i=levelToUpdate; i>=0; i--) {\n";
	    print MODEL "	  if(i==noLevels-1) {\n";
	    print MODEL "	    memcpy(&partialImages[i],&original_s,vsize); \n";
	    print MODEL "	  } else {\n";
	    print MODEL "	    memcpy(&partialImages[i],&partialImages[i+1],vsize);\n";
	    print MODEL "	  }\n";
	    print MODEL "	  applyPermToState(&partialImages[i],&traversalChain[i][levelCounters[i]]);\n";
	    print MODEL "	}\n";
	    print MODEL "	break;\n";
	    print MODEL "       } else {\n";
	    print MODEL "         levelCounters[levelToUpdate++]=0;\n";
	    print MODEL "       }\n";
	    print MODEL "    }\n";
	    print MODEL "  }\n";
	    print MODEL "}\n";
	    
	} elsif($flatten) {
	    print MODEL "void flatten(State *s) {\n";
	    print MODEL "  /* JAVA */\n";
	    print MODEL "}\n\n";
	} elsif($markers) {
	    print MODEL "/* MARKER */\n\n";
	    if($markerstype eq "BOSNACKIMARKERS") {
		print MODEL "int offset = 5;\n\n";
	    }
	    if($markerstype eq "APPROXMARKERS") {
		print MODEL "/* MARKPIDS */\n\n";
	    }
	}

	if(!$markers) {

	    $setcounter = 1;
	    # NOW LOOK IN THE GROUP INFO FILE AND PUT THE APPROPRIATE DECLARATIONS
	    for($group_info_counter = 0; $group_info_counter<scalar(@group_info); $group_info_counter++) {
		if($group_info[$group_info_counter] =~ /</) {
		
		    if($useStabiliserChain && ($group_info[$group_info_counter] =~ /<enumerate>/)) {
			print MODEL "struct perm* elementset_";
		    } else {
			print MODEL "struct perm elementset_";
		    }
		    print MODEL $setcounter;
		    print MODEL "[";
		    print MODEL trimwhitespace($group_info[$group_info_counter+1]);
		    print MODEL "];\n";
		    $setcounter++;
		}
	    }
	}

	print MODEL "\nState *rep(State *orig_now) {\n\n";

	if($markers) {

	    my $procsminus1 = $ARGV[1]-1;

	    # FOR SIMPLICITY, I HAVE INCLUDED DUPLICATE CODE FOR EACH MARKERS STRATEGY.

	    if($markerstype eq "EXACTMARKERS") {

		# EXACTMARKERS

		print MODEL "   Marker markers[$procsminus1], temp;\n";
		print MODEL "   int i, j;\n";
		print MODEL "   memcpy(&min_now,orig_now,vsize);\n";
		print MODEL "   for(i=0; i<$procsminus1; i++) {\n";
		print MODEL "      mark(&markers[i],orig_now,i+1);\n";
		print MODEL "   }\n";
		print MODEL "   for(i=0; i<";
		print MODEL $procsminus1-1;
		print MODEL "; i++) {\n";
		print MODEL "      for(j=i+1; j<$procsminus1; j++) {\n";
		print MODEL "         if(lt(&markers[i],&markers[j])) {\n";
		print MODEL "            memcpy(&temp,&markers[i],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[i],&markers[j],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[j],&temp,sizeof(Marker));\n";
		print MODEL "            applyPrSwapToState(&min_now,i+1,j+1);\n";
		print MODEL "         }\n";
		print MODEL "      }\n";
		print MODEL "   }\n";

	    } elsif($markerstype eq "APPROXMARKERS") {

		#APPROXMARKERS

		print MODEL "   Marker markers[$procsminus1], orig_markers[$procsminus1], temp;\n";
		print MODEL "   State tempstate;\n";
		print MODEL "   int i, j, map[$procsminus1];\n\n";

		print MODEL "   memcpy(&min_now,orig_now,vsize);\n";
		print MODEL "   for(i=0; i<$procsminus1; i++) {\n";
		print MODEL "      mark(&markers[i],orig_now,i+1);\n";
		print MODEL "   }\n\n";
		print MODEL "   memcpy(orig_markers,markers,$procsminus1*sizeof(Marker));\n\n";

		print MODEL "   for(i=0; i<";
		print MODEL $procsminus1-1;
		print MODEL "; i++) {\n";
		print MODEL "      for(j=i+1; j<$procsminus1; j++) {\n";
		print MODEL "         if(lt(&markers[i],&markers[j])) {\n";
		print MODEL "            memcpy(&temp,&markers[i],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[i],&markers[j],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[j],&temp,sizeof(Marker));\n";
		print MODEL "            applyPrSwapToState(&min_now,i+1,j+1);\n";
		print MODEL "         }\n";
		print MODEL "      }\n";
		print MODEL "   }\n\n";
		print MODEL "   for(i=0; i<$procsminus1; i++) {\n";
		print MODEL "      for(j=";
		print MODEL $procsminus1-1;
		print MODEL "; j>=0; j--) {\n";
		print MODEL "         if(eq(&markers[j],&orig_markers[i])) {\n";
		print MODEL "            map[i] = j;\n";
		print MODEL "            break;\n";
		print MODEL "         }\n";
		print MODEL "      }\n";
		print MODEL "   }\n\n";

		print MODEL "   markPIDs(&min_now,map);\n";

	    } else {

		# BOSNACKI MARKERS

		print MODEL "   Marker *markers, temp;\n";
		print MODEL "   int i, j;\n";
		print MODEL "   markers = (Marker*)(((char*)&min_now)+offset);\n";
		print MODEL "   for(i=0; i<$procsminus1; i++) {\n";
		print MODEL "      mark(&markers[i],orig_now,i+1);\n";
		print MODEL "   }\n";
		print MODEL "   for(i=0; i<";
		print MODEL $procsminus1-1;
		print MODEL "; i++) {\n";
		print MODEL "      for(j=i+1; j<$procsminus1; j++) {\n";
		print MODEL "         if(memcmp(&markers[i],&markers[j],sizeof(Marker))<0) {\n";
		print MODEL "            memcpy(&temp,&markers[i],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[i],&markers[j],sizeof(Marker));\n";
		print MODEL "            memcpy(&markers[j],&temp,sizeof(Marker));\n";
		print MODEL "         }\n";
		print MODEL "      }\n";
		print MODEL "   }\n";
		if(!$exactmarkers) {
		    print MODEL "   for(i=$procsminus1*sizeof(Marker)+offset; i<vsize; i++) {\n";
		    print MODEL "      ((char*)&min_now)[i]=0;\n";
		    print MODEL "   }\n";
		}
	    }
	} else {

	    print MODEL "  int j;\n\n";
	    print MODEL "  memcpy(&min_now, orig_now, vsize);\n";

	    # STRATEGIES GO HERE
	    if($flatten) {
		print MODEL "  flatten(&min_now);\n";
	    }

	    $group_info_counter = 0;
	    $setcounter = 1;
	    while($group_info_counter<scalar(@group_info)) {

		# ENUMERATION STRATEGY WITH SIMS METHOD
		if($useStabiliserChain && ($group_info[$group_info_counter] =~ /<enumerate>/)) { 
		    $stabchainsize = trimwhitespace($group_info[$group_info_counter+1]);

		
		    # make an array which stores the number of reps for each partitioning
		    $partitionCounter = 0;
		    my @partitionSize;

		    while($partitionCounter<$stabchainsize) {
			if($group_info[$group_info_counter] =~ /coset/) {
			    @cosetInfo = split(/:/,$group_info[$group_info_counter]);
			    $partitionSize[$partitionCounter] = trimwhitespace($cosetInfo[1]);
			    $partitionCounter++;
			}
			$group_info_counter++;
		    }

		    print MODEL "  {\n";

		    print MODEL "  int ";
		    for($partitionCounter=0; $partitionCounter<$stabchainsize; $partitionCounter++) {
			print MODEL "i$partitionCounter";
			if($partitionCounter<($stabchainsize-1)) {
			    print MODEL ", ";
			} else {
			    print MODEL ";\n\n";
			}
		    }

		    print MODEL "  State partialImages[$stabchainsize];\n\n";

		    print MODEL "  State originalForThisStrategy;\n";
		    print MODEL "  memcpy(&originalForThisStrategy,&min_now,vsize);\n\n";

		    for($partitionCounter=0; $partitionCounter<$stabchainsize; $partitionCounter++) {

			for($whiteSpaceCounter=0; $whiteSpaceCounter<$partitionCounter+1; $whiteSpaceCounter++) {
			    print MODEL "  ";

			}

			$partitionIndex = $stabchainsize-$partitionCounter-1;
			print MODEL "for(i$partitionIndex=0; i$partitionIndex<";
			print MODEL $partitionSize[$partitionIndex];
			print MODEL "; i$partitionIndex++) {\n";

			for($whiteSpaceCounter=0; $whiteSpaceCounter<$partitionCounter+2; $whiteSpaceCounter++) {
			    print MODEL "  ";

			}
		    
			if($partitionCounter==0) {
			    print MODEL "memcpy(&partialImages[$partitionIndex],&originalForThisStrategy,vsize);\n";
			} else {
			    print MODEL "memcpy(&partialImages";
			    print MODEL "[$partitionIndex],&partialImages[";
			    print MODEL $partitionIndex+1;
			    print MODEL "],vsize);\n";
			}


			for($whiteSpaceCounter=0; $whiteSpaceCounter<$partitionCounter+2; $whiteSpaceCounter++) {
			    print MODEL "  ";

			}

			print MODEL "applyPermToState(&partialImages";
			print MODEL "[$partitionIndex],&elementset_$setcounter";
			print MODEL "[$partitionIndex][i";
			print MODEL "$partitionIndex]);\n\n";

		    }

		    for($partitionCounter=0; $partitionCounter<$stabchainsize; $partitionCounter++) {
			print MODEL "  ";
		    }

		    print MODEL "  if(";
		    print MODEL compare("&partialImages[0]","&min_now");
		    print MODEL ") {\n";
		    for($partitionCounter=0; $partitionCounter<$stabchainsize; $partitionCounter++) {
			print MODEL "  ";
		    }
		    
		    print MODEL "    memcpy(&min_now,&partialImages[0],vsize);\n";
		    
		    for($partitionCounter=0; $partitionCounter<$stabchainsize; $partitionCounter++) {
			print MODEL "  ";
		    }
		    
		    print MODEL "  }\n";
		    
		    for($partitionIndex=$stabchainsize; $partitionIndex>0; $partitionIndex--) {
			for($partitionCounter=0; $partitionCounter<$partitionIndex; $partitionCounter++) {
			    print MODEL "  ";
			}
			
			print MODEL "}\n";
			
		    }
		    
		    print MODEL "  } /* End of sims enumeration */\n";
		    
		    
		    $setcounter++;
		}

		# ENUMERATION STRATEGY
		if((!$useStabiliserChain) && $group_info[$group_info_counter] =~ /<enumerate>/) { 
		    $setsize = trimwhitespace($group_info[$group_info_counter+1]);
		    
		    print MODEL "  memcpy(&tmp_now, orig_now, vsize);\n"; 
		    print MODEL "  memcpy(&current_min, &min_now, vsize);\n";
		    
		    print MODEL "  for(j=0; j<$setsize; j++) {\n";
		    print MODEL "    applyPermToState(&tmp_now,&(elementset_$setcounter\[j\]));\n"; 
		    print MODEL "    if(";
		    print MODEL compare("&tmp_now","&current_min");
		    print MODEL ")\n";
		    print MODEL "      memcpy(&current_min,&tmp_now,vsize);\n"; 
		    print MODEL "    memcpy(&tmp_now,&min_now,vsize);\n";
		    print MODEL "  }\n";
		    print MODEL "  memcpy(&min_now,&current_min,vsize);\n\n";
		    
		    $setcounter++;
		}
		
		# MINIMISING SET STRATEGY
		if($group_info[$group_info_counter] =~ /<minimise>/) {
		    $setsize = trimwhitespace($group_info[$group_info_counter+1]);
		    
		    print MODEL "  do {\n";
		    print MODEL "    memcpy(&current_min,&min_now,vsize);\n\n";
		    
		    print MODEL "    for(j=0; j<$setsize; j++) {\n";
		    print MODEL "      memcpy(&tmp_now,&min_now,vsize);\n";
		    print MODEL "      applyPermToState(&tmp_now,&(elementset_$setcounter\[j\]));\n";   # this could probably be made more efficient
		    print MODEL "      if(";
		    print MODEL compare("&tmp_now","&min_now");
		    print MODEL ")\n";
		    print MODEL "        memcpy(&min_now,&tmp_now,vsize);\n";
		    print MODEL "    }\n";
		    print MODEL "  } while(memcmp(&min_now,&current_min,vsize)!=0);\n\n";
		    $setcounter++;
		}
		
		# LOCAL SEARCH STRATEGY
		if($group_info[$group_info_counter] =~ /<localsearch>/) {
		    $setsize = trimwhitespace($group_info[$group_info_counter+1]);
		    
		    print MODEL "  do {\n";
		    print MODEL "    memcpy(&current_min,&min_now,vsize);\n\n";
		    
		    print MODEL "    for(j=0; j<$setsize; j++) {\n";
		    print MODEL "      memcpy(&tmp_now,&current_min,vsize);\n";
		    print MODEL "      applyPermToState(&tmp_now,&(elementset_$setcounter\[j\]));\n";   # this could probably be made more efficient
		    print MODEL "      if(";
		    print MODEL compare("&tmp_now","&min_now");
		    print MODEL ")\n";
		    print MODEL "        memcpy(&min_now,&tmp_now,vsize);\n";
		    print MODEL "    }\n";
		    print MODEL "  } while(memcmp(&min_now,&current_min,vsize)!=0);\n\n";
		    $setcounter++;
		}
		
		$group_info_counter++;
		
	    }
	    
	    if($segment) {
		print MODEL "  segment(&min_now);\n\n";
	    }
	}	    
	print MODEL "  return &min_now;\n";
	print MODEL "}\n\n";
    }

    if(($lines[$counter] =~ /if \(signoff\)/) && $segment) {
        print MODEL "   printf(\"Number of stabilisers: %d\\n\",noStabilisers);\n";
	print MODEL "   printf(\"stp\\n\");\n";
    }

    if($lines[$counter] =~ /void to_compile\(void\);/) { # When the main method is reached, add code to initialise
	     # symmetry group.  If we're using markers don't do this, but initialise offset if necessary.

	if($markers) {
#	    if($markerstype eq "BOSNACKIMARKERS") {
#		print MODEL "   offset = sizeof(uchar) + sizeof(uchar) + sizeof(uchar)\n";
#		print MODEL "#ifndef NOFAIR\n";
#		print MODEL "      + NFAIR*sizeof(uchar)\n";
#		print MODEL "#endif\n";
#		print MODEL "#ifndef NOVSZ\n";
#		print MODEL "#if VECTORSZ<65536\n";
#		print MODEL "      + sizeof(unsigned short)\n";
#		print MODEL "#else\n";
#		print MODEL "      + sizeof(unsigned long)\n";
#		print MODEL "#endif\n";
#		print MODEL "#endif\n";
#		print MODEL "#ifdef HAS_LAST\n";
#		print MODEL "      + sizeof(uchar);\n";
#		print MODEL "#endif\n";
#		print MODEL "#ifdef EVENT_TRACE\n";
#		print MODEL "#if nstates_event<256\n";
#		print MODEL "      + sizeof(uchar);\n";
#		print MODEL "#else\n";
#		print MODEL "      + sizeof(unsigned short)\n";
#		print MODEL "#endif\n";
#		print MODEL "#endif\n";
#		print MODEL ";\n\n";
#	    }
	} else {

	    # LOOK IN THE GROUP INFO FILE AND FILL UP THE ARRAYS FOR EACH SET

	    if($segment) {
		print MODEL "  printf(\"grp:Group($groupGenerators);\\n\");\n\n";
	    }

	    $setcounter = 0;
	    $index = 0;
	    for($group_info_counter=0; $group_info_counter< scalar(@group_info); $group_info_counter++) {
		
		# Sims method
		if($useStabiliserChain && ($group_info[$group_info_counter] =~ /<enumerate>/)) {
		    
		    $setcounter++;
		    
		    $noPartitions = trimwhitespace($group_info[$group_info_counter+1]);
		    
		    $group_info_counter = $group_info_counter+2;
		    $partitionCounter = 0;
		    
		    while($partitionCounter < $noPartitions) {
			
			@cosetInfo = split(/:/,$group_info[$group_info_counter]);
			$group_info_counter++;
			# intValue
			$partitionSize = trimwhitespace($cosetInfo[1]);
			
			print MODEL "\n  elementset_$setcounter";
			print MODEL "[$partitionCounter] = malloc($partitionSize * sizeof(struct perm));\n";
			
			if($useTranspositions) {
			    print MODEL "  elementset_$setcounter";
			    print MODEL "[$partitionCounter][0] = constructPerm(\"\");\n";
			} else {
			    print MODEL "  elementset_$setcounter";
			    print MODEL "[$partitionCounter][0] = constructPerm(\"()\");\n";
			}
			
			for($cosetrepCounter=1; $cosetrepCounter<$partitionSize; $cosetrepCounter++) {
			    print MODEL "  elementset_$setcounter";
			    print MODEL "[$partitionCounter][$cosetrepCounter] = constructPerm(\"";
			    
			    my $perm = $group_info[$group_info_counter];
			    
			    while($perm =~ /\\/ ) {
				$perm = substr($perm,0,length($perm)-2);
				$group_info_counter = $group_info_counter + 1;
				$perm = $perm . $group_info[$group_info_counter];
			    }
			    
			    if($useTranspositions) {
				print MODEL trimwhitespace($perm);
			    } else {
				print MODEL convertPerm(trimwhitespace($perm));
			    }
			    
			    print MODEL "\\0\");\n";
			    
			    $group_info_counter++;
			}
			$partitionCounter++;
			
		    }
		    
		}
		
		else {
		    if($group_info[$group_info_counter] =~ /</) {
			#skip the line which says how many permutations there will be
			$group_info_counter++;
			$setcounter++;
			$index = 0;
		    }
		    
		    #if($group_info[$group_info_counter] =~ /\(/) {
		    else {
			print MODEL "  elementset_";
			print MODEL "$setcounter";
			print MODEL "[$index]=constructPerm(\"";
			
			my $perm = $group_info[$group_info_counter];
			while($perm =~ /\\/ ) {
			    $perm = substr($perm,0,length($perm)-2);
			    $group_info_counter = $group_info_counter + 1;
			    $perm = $perm . $group_info[$group_info_counter];
			    
			}
			
			if($useTranspositions) {
			    print MODEL trimwhitespace($perm);
			} else {
			    print MODEL convertPerm(trimwhitespace($perm));
			}
			print MODEL "\\0\");\n";
			$index++;
		    }
		}
	    }
	}
    }
}

close(MODEL);

# DEAL WITH group.h

open(GROUP, "group.h");                                  # Read in "group.h"       
@lines = <GROUP>;
close(GROUP);

open(GROUP, ">group.h");
for($counter=0; $counter<scalar(@lines); $counter++) {   # Set number of processes, channels and generators
    $lines[$counter] =~ s/<NO_PROCS>/$ARGV[1]/;          # appropriately.
    $lines[$counter] =~ s/<NO_CHANS>/$ARGV[2]/;
    print GROUP "$lines[$counter]";
}
close(GROUP);

if(!$exactmarkers) {
    system("gcc","-c","group.c");                            # Compile the group theory code.
}
