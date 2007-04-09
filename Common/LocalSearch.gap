LocalsearchGroup := function(G)

  local result, alpha;

  result := "";

  result := Concatenation(result,"<localsearch>\n",String(Size(GeneratorsOfGroup(G))),"\n");
  for alpha in GeneratorsOfGroup(G) do
    result := Concatenation(result,PermToString(alpha),"\n");
  od;
  return result;

end;;

ClassifyLocalSearch := function(G,fname)

  local output;

  output := LocalsearchGroup(G);

  PrintTo(fname,output);

end;;
