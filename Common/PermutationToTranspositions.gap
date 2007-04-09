PermutationToTranspositions := function (pi)

    local res, cycle, start, pnt;

res := [];

while pi <> () do

    # compute decomposition of cycle starting
    #with smallest moved point

    cycle := [];
    start := SmallestMovedPointPerm (pi);
    pnt := start^pi;

# now get the decomposition
# (p_1, p_2, ..., p_n) = (p_1, p_2)(p_1, p_3)...(p_1, p_n)

    repeat
    Add (cycle, (start, pnt));
    Add(res,start);
    Add(res,pnt);
    pnt := pnt^pi;
    until pnt = start;

    # multiply pi by the inverse of the cycle
    pi := pi * Product (Reversed (cycle));

od;
return res;
end; 
