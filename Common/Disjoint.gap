ComputeDisjointDecomposition := function(G)

  local gens, i, j, DecompositionGenerators, R, E, Classes;

  gens := GeneratorsOfGroup(G);

  R := [];

  for i in [1..Size(gens)] do
    Add(R,[]);
  od;

  for i in [1..Size(gens)-1] do

    for j in [i+1..Size(gens)] do

	if not(Intersection(MovedPoints(gens[i]),MovedPoints(gens[j])) = []) then
		Add(R[i],j);
        fi;

    od;

  od;

  E := EquivalenceRelationByRelation(BinaryRelationOnPoints(R));

  Classes := EquivalenceClasses(E);

  if Size(Classes)=1 then
    return fail;
  fi;

  DecompositionGenerators := [];

  for i in [1..Size(Classes)] do
    Add(DecompositionGenerators,[]);
    for j in [1..Size(gens)] do
      if EquivalenceClassOfElement(E,j)=Classes[i] then
         Add(DecompositionGenerators[i],gens[j]);
      fi;
    od;
  od;

  return List(DecompositionGenerators,x -> Group(x));

end;;
