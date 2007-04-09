useTranspositions := true;
useStabiliserChain := true;

Read("PermutationToTranspositions.gap");;
Read("StabilizerChainCosets.gap");;
Read("OutputPerm.gap");;
Read("EnumerationStrategies.gap");;

G := Group(());

Verify := function(command)

   local topspin, line, splitLine, H, S, U, i, j, p, partitions, partitionMembers;

   topspin := InputOutputLocalProcess(DirectoryCurrent(),Filename(DirectoryCurrent(),command),[]);

#   stabilisers := [];

   while true do

     line := ReadLine(topspin);

     if line = "stp\n" then
  
        break;

     fi;

     splitLine := SplitString(line,":");
    
     if splitLine[1] = "grp" then

	Read(InputTextString(Concatenation("G := ",splitLine[2])));
	#Print(G,"\n");

     else 
        if splitLine[1] = "ptn" then 

	   #Print(splitLine[2]);

	    H := G;

	    partitions := SplitString(splitLine[2],"|");

            for p in partitions do

		partitionMembers := SplitString(p,",","\n");

		S := [];

		for i in partitionMembers do
		   Add(S,Int(i));
		od;

		H := Stabilizer(H,S,OnSets);

             od;

             #if not (H in stabilisers) then
             #      Add(stabilisers,H);
	#	  Print(Size(stabilisers),"\n");
         #    fi;


	     #Print(H,"\n");

	     if not (H = Group(())) then
		     U := StabChainCosetReps(H);

        	     WriteLine(topspin,String(Size(U)));

	             for i in [1..Size(U)] do
	       	        WriteLine(topspin,String(Size(U[i])));
			for j in [2..Size(U[i])] do
                	  WriteLine(topspin,PermToString(U[i][j]));
                	od;
             	    od;
             else
		WriteLine(topspin,"identity");
             fi;


	else

            Print(line);

          fi;

     fi;

   od;

end;


