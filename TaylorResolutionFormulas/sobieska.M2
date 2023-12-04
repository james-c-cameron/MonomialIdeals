sobieska = method()
sobieska(ZZ,MonomialIdeal,RingElement):= (n,I,f)->(
   --- create the degree n Sobieska homotopy of f 
    retVal := Nothing;
   if (n == 0) then 
      R:= ring I
      retVal = f//gens I
   else
   {
      idealList := flatten entries gens I;
      R := ring I;
      sourceSubsets := subsets(toList (0..(numgens I - 1)),n);
      targetSubsets := subsets(toList (0..(numgens I - 1)),n+1);
      sourceList := apply(sourceSubsets, i -> myLcm(idealList_i));
      targetList := apply(targetSubsets, i -> myLcm(idealList_i));
      getCoeff := (i,j) -> if (isSubset(sourceSubsets_i,targetSubsets_j)) then
                             (-1)^(position(targetSubsets_j, k -> k == (toList(set targetSubsets_j - set sourceSubsets_i))_0))
			   else 0_R;
      myFn := (i,j) -> (tempElt :=( sourceList_j *idealList_(toList(set targetSubsets_j - set sourceSubsets_i)_0) / targetList_i)*(f//gens I)_(toList(set targetSubsets_j - set sourceSubsets_i)_0);
	                if (liftable(tempElt,R)) then getCoeff(i,j)*lift(tempElt,R) else 0_R);
      retVal = map(R^(-apply(targetList, i -> degree i)), R^(-apply(sourceList, i -> degree i)), myFn);
   };
   retVal
)

taylorResolution=method(
    Options => {LengthLimit => 0}
)
taylorResolution(MonomialIdeal):= o -> (I)->(
    --- this function just returns the Koszul complex
    --- where I represents the first differential.
    if not instance(o.LengthLimit, ZZ)
    then error "The optional LengthLimit must be an integer.";
    lengthLimit := 0;
    if (o.LengthLimit == 0) then
       lengthLimit = numgens I
    else
       lengthLimit = o.LengthLimit;
    chainComplex(apply((1..lengthLimit), i -> taylor(i,I)))
)

position({1,2,4}, k -> k == (toList(set {1,2,4} - set {2,4}))_0)
