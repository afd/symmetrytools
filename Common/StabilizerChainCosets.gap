StabChainCosetReps := function(G)

  local U, i, finished, chain;

  U := [];
  i := 1;

  chain := StabChain(G);

  while true do
	if chain.stabilizer.generators = [] then
          U[i] := RightTransversal(Group(chain.generators),Group(()));
          break;
        else
          U[i] := RightTransversal(Group(chain.generators),Group(chain.stabilizer.generators));
          i := i+1;
          chain := chain.stabilizer;
        fi;
  od;

  return U;

end;;

DisplayCosetRepsList := function(U)

  local i, j;

  Print("[ ");
  
  for i in [1..Size(U)] do
    Print("[");

      for j in [1..Size(U[i])] do
        Print(U[i][j]);
        if j<Size(U[i]) then
          Print(",");
        fi;
      od;


    Print("] ");

    if i<Size(U) then
      Print(", ");
    fi;

  od;

  Print(" ]\n");

end;;

ListElements := function(alpha,U)

  local result, i;

  if alpha = 1 then
     alpha := ();
  fi;

  result := [];

  for i in [1..Size(U[1])] do

    if Size(U) = 1 then
       Add(result,U[1][i]*alpha);
    else
       result := Concatenation(result,ListElements(U[1][i]*alpha,U{[2..Size(U)]}));
    fi;
  od;
  
  return result;

end;;

ListGroupElements := function(G)
  return ListElements(1,StabChainCosetReps(G));
end;
  
