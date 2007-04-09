# Requires PermutationToTranspositions.gap to have been loaded,
# and assumes that useTranspositions has been set to a boolean value

PermToString := function(alpha)
  local i, result, swapsList;

  if(useTranspositions) then
    result := "";
    swapsList := PermutationToTranspositions(alpha);
    for i in [1..Size(swapsList)] do
      result := Concatenation(result,String(swapsList[i]));
      if(i<Size(swapsList)) then
        result := Concatenation(result," ");
      fi;
    od;
    return result;
  else
    return String(alpha);
  fi;

end;;
