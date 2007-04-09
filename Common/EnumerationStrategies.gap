EnumerateGroup := function(G)

  local result, alpha;

  result := Concatenation("","<enumerate>\n",String(Size(G)-1),"\n");
  for alpha in G do
    if (not(alpha=())) then
      result := Concatenation(result,PermToString(alpha),"\n");
    fi;
  od;
  return result;

end;;

EnumerateGroupByStabilizerChainCosets := function(G)

   local U, i, j, result;

   U := StabChainCosetReps(G);

   result := Concatenation("","<enumerate>\n",String(Size(U)),"\n");
   for i in [1..Size(U)] do
     result := Concatenation(result,"coset:",String(Size(U[i])),"\n");
     for j in [2..Size(U[i])] do
       result := Concatenation(result,PermToString(U[i][j]),"\n");
     od;
   od;
   return result;
end;;
