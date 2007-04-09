ClassifyEnumerate := function(G,fname)

  if(useStabiliserChain) then
    PrintTo(fname,EnumerateGroupByStabilizerChainCosets(G));
  else
    PrintTo(fname,EnumerateGroup(G));
  fi;
end;;
