DegreeActionParentGroup := 0;

Classify := function(G)

  local A, i, result, alpha;

  A := ComputeMinimisingSet(G);

  if not (A=fail) then

    # Minimising Set

    #Print("Minimising set: ",A,"\n\n");

    result := Concatenation("<minimise>\n",String(Size(A)),"\n");
    for i in [1..Size(A)] do
      result := Concatenation(result,PermToString(A[i]),"\n");
    od;


    return result;
  fi;

  A := ComputeDisjointDecomposition(G);
  if not (A=fail) then

    # Classify Factors of Disjoint Product

    #Print("Disjoint product: ",A,"\n\n");

    result := "<parallel>\n";
    for i in [1..Size(A)] do
      Classify(A[i]);

      result := Concatenation(result,Classify(A[i]));
    od;
    result := Concatenation(result,"</parallel>\n");

    return result;
  fi;

  A := ComputeWreathDecomposition(G);
  if not(A=fail) then

    # Classify Factors of Wreath Product

    #Print("Wreath product: ",A,"\n\n");

    result := "<parallel>\n";
    
    for i in [1..Size(A)-1] do
      Classify(A[i]);

      result := Concatenation(result,Classify(A[i]));
    od;

    result := Concatenation(result,"</parallel>\n");

    result := Concatenation(result, Classify(A[Size(A)]));

    return result;

  fi;

  if Size(G)<=DegreeActionParentGroup^2 then

    # Enumerate

    #Print("Enumeration");

    if(useStabiliserChain) then
      return EnumerateGroupByStabilizerChainCosets(G);
    else
      return EnumerateGroup(G);
    fi;
    

    return;
  fi;

  # Group is unclassifiable, so use local search
  result := Concatenation(result,"<localsearch>\n",String(Size(GeneratorsOfGroup(G))),"\n");
  for alpha in GeneratorsOfGroup(G) do
    result := Concatenation(result,PermToString(alpha),"\n");
  od;
  return result;

end;

ClassifyBest := function(G,fname)

  local newGens, alpha;

  # Ensure that identity is not included as a generator
  newGens := [];
  for alpha in GeneratorsOfGroup(G) do
    if not((alpha=()) or (alpha in newGens)) then
      Add(newGens,alpha);
    fi;
  od;

  DegreeActionParentGroup := DegreeAction(G);

  PrintTo(fname,Classify(Group(newGens)));

end;;

TestGroup := function()
  local H, G1, K, L;

  H := Group([ (1,2),(3,4),(5,6),(7,8),(9,10,11,12)(1,3,5,7)(2,4,6,8),(9,10)(1,3)(2,4)(11,12)(5,7)(6,8) , (13,14)(15,16) ]);

  G1 := WreathProduct(H,SymmetricGroup(3));
 
  K := Group([ (49,50),(51,52),(49,51)(50,52)(53,54) ]);

  L := Group([ (55,56,57) ]);

  return Group(Concatenation(GeneratorsOfGroup(G1),GeneratorsOfGroup(L),GeneratorsOfGroup(K)));

end;