ComputeMinimisingSet := function(G)
 
  local O, O2, i, j, Columns, H, phi, result;

  if Size(G)<=2 then
    return fail;
  fi;

  O := Orbits(G);

  for i in [2..Size(O)] do
    if not (Size(O[i])=Size(O[1])) then
      return fail;
    fi;
  od;

  Columns := [];

  for i in [1..Size(O[1])] do
    Add(Columns,[O[1][i]]);

    H := Stabilizer(G,O[1][i]);

    for j in [2..Size(O)] do
      O2 := Orbits(H,O[j]);
      if not Size(O2)=2 then
        return fail;
      fi;

      if Size(O2[1])=1 then
        Add(Columns[i],O2[1][1]);
      else 
        if Size(O2[2])=1 then
          Add(Columns[i],O2[2][1]);
        else
          return fail;
        fi;
      fi;
    od;

  od;

  for i in [1..Size(Columns)] do
    Sort(Columns[i]);
  od;

  if not (Size(G)=Factorial(Size(Columns))) then
    return fail;
  fi;

  phi := ActionHomomorphism(G,Columns,OnSets);

  H := ImagesSource(phi);

  result := [];

  for i in [1..DegreeAction(H)-1] do
    for j in [i+1..DegreeAction(H)] do
      Add(result,PreImagesRepresentative(phi,(i,j)));
    od;
  od;

  return result;

end;