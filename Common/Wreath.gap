FindBlockPosition := function(c,H)
  local i;
  for i in [1..Size(H)] do
    if Size(Orbits(H[i],c))>1 then
      return i;
    fi;
  od;

  return fail;

end;

ComputePseudoBlockSystem := function(G,BList)

  # BList is a list of equally sized block systems, each of which works on a different orbit of G.

  local A, B, C, H, i, c, o, A2;

  B := BList[1];

  A := [];
  H := [];
  for i in [1..Size(B)] do
    A[i] := B[i];
    H[i] := Stabilizer(Stabilizer(G,B[i],OnSets),B[i][1]);
  od;

  for i in [2..Size(BList)] do
    C := BList[i];
    for c in C do
      i := FindBlockPosition(c,H);
      if i = fail then
        for i in [1..Size(C)] do
          A[i] := Concatenation(A[i],C[i]);
          H[i] := Stabilizer(Stabilizer(H[i],C[i],OnSets),C[i][1]);
        od;
        break;
      else
        A[i] := Concatenation(A[i],c);
      fi;
    od;
  od;

  A2 := [];
  for i in [1..Size(A)] do
    A2[i] := ShallowCopy(A[i]);
    Sort(A2[i]);
  od;

  return A2;

end;

ComputeBottomGroup := function(G,A)

  # A is a pseudo block system

  local i, j, k, Bottom;

  Bottom := [];

  for i in [1..Size(A)] do
     Bottom[i] := G;
     for j in [1..Size(A)] do
       if not (j=i) then
         for k in A[j] do
           Bottom[i] := Stabilizer(Bottom[i],k);
         od;
       fi;
     od;
  od;
  return Bottom;
end;

ComputeTopGroup := function(G,A,Size_H)

  local phi, K, alpha, i, j, GeneratorsOfResult, permAsList;

  phi := ActionHomomorphism(G,A,OnSets);

  K := ImagesSource(phi);


  if not (Size(G) = Size_H^Size(A) * Size(K)) then
    return fail;
  fi;

  GeneratorsOfResult := [];

  for alpha in GeneratorsOfGroup(K) do
    permAsList := [];
    for i in [1..Maximum(MovedPoints(G))] do
      Add(permAsList,i);
    od;

    for i in MovedPoints(alpha) do
       for j in [1..Size(A[1])] do
         permAsList[A[i][j]] := A[i^alpha][j];
       od;
    od;

    Add(GeneratorsOfResult,PermList(permAsList));

  od;

 
  if IsSubgroup(G,Group(GeneratorsOfResult)) then
    return Group(GeneratorsOfResult);
  fi;
  # ASSERT FALSE
  return fail;

end;

AllBlockSystems := function(G)

  # G is assumed to be transitive

  local B, i, result, B_unmutable;


  result := [];
  B_unmutable := AllBlocks(G);

  B := ShallowCopy(B_unmutable);

  Add(B,[Orbits(G)[1][1]]);

  for i in [1..Size(B)] do
    Add(result,Orbit(G,B[i],OnSets));
  od;

  return result;

end;

InitialiseCounter := function(n)
  local counter, i;
  counter := [];
  for i in [1..n] do
    Add(counter,1);
  od;
  return counter;
end;

ResetCounter := function(counter)
  local i;
  for i in [1..Size(counter)] do
    if not (counter[i] = 1) then
      return false;
    fi;
  od;
  return true;
end;

ComputeWreathDecomposition := function(G)

  local O, AllBlockSystemsForOrbit, i, A, equalsizes, equalsizedblocksystems, Bottom, Top, counter;

  O := Orbits(G);

  AllBlockSystemsForOrbit := [];

  for i in [1..Size(O)] do
    Add(AllBlockSystemsForOrbit,AllBlockSystems(Group(List(GeneratorsOfGroup(G),x->RestrictedPerm(x,O[i])))));
  od;

  counter := InitialiseCounter(Size(O));

  while true do

    equalsizes := true;
    for i in [1..Size(O)] do
      if not (Size(AllBlockSystemsForOrbit[i][counter[i]]) = Size(AllBlockSystemsForOrbit[1][counter[1]])) then
        equalsizes := false;
        break;
      fi;
    od;

    if equalsizes then

      equalsizedblocksystems := [];
      for i in [1..Size(O)] do
        Add(equalsizedblocksystems,AllBlockSystemsForOrbit[i][counter[i]]);
      od;

      A := ComputePseudoBlockSystem(G,equalsizedblocksystems);

      Bottom := ComputeBottomGroup(G,A);

      if Size(Bottom[1])>1 then

        Top := ComputeTopGroup(G,A,Size(Bottom[1]));
        if not (Top = fail) then

          if ( G = Group(Concatenation(GeneratorsOfGroup(Bottom[1]),GeneratorsOfGroup(Top)))) then
            return Concatenation(Bottom,[Top]);
          fi;
        fi;
      fi;
    fi;

    # Update counter

    i := Size(O);
    while i>=1 do
      if counter[i]<Size(AllBlockSystemsForOrbit[i]) then
        counter[i] := counter[i]+1;

        break;
      else
        counter[i] := 1;
        i := i-1;
      fi;
    od;

    if ResetCounter(counter) then
      break;
    fi;

  od;

  return fail;

end;




## TEST GROUPS

ThreeTieredGroup := function()
   return Group((1,2,3,4)(13,14,15,16),(2,3)(14,15),(5,6,7,8)(17,18,19,20),
     (6,7)(18,19),(9,10,11,12)(21,22,23,24),(10,11)(22,23),
     (25,26,27)(1,5,9)(2,6,10)(3,7,11)(4,8,12)(13,17,21)(14,18,22)(15,19,23)(16,20,24),
     (1,5)(2,6)(3,7)(4,8)(13,17)(14,18)(15,19)(16,20)(25,26));
end;

