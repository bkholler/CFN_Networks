load "sunletQuadGens.m2"

-- Tries to find a sequence of prime ideals as described in Section 6
-- If successful then this gives a proof of primality but failure
-- does not guarantee reducibility. As coded, this is a heuristic approach
-- but has succeeded in every example we can compute.
attemptPrimeDescent = J -> (

  R := ring J;

  gensR := gens R;

  idealList := {J};

  isJPrime = false;
  validSequence := true;

  for x in drop(reverse(gensR), sub((-(# gensR)/2), ZZ)) do(

    I := idealList_(-1);

    if not (isSubset({x}, support I)) then continue;

    foundf = false;

    for f in (flatten entries gens I) do(

      suppf := support f;

      if not isSubset({x}, suppf) then continue;

      g = f // x;
      h = f % x;

      if isSubset({x}, support h) then continue;
      if isSubset({x}, support g) then continue;

      if g % J == 0 then continue else(

        foundf = true;
        break;
        );
      );


    if foundf then idealList = append(idealList, eliminate(x, I)) else(

      validSequence = false;
      print(concatenate("Prime descent failed at: ", toString(x)));
      break;
      );
    );

    if validSequence then(

      isJPrime = true;
      print("Prime descent succeeded. J is Prime.")
      );

    return isJPrime;
    );




-- Makes a list which records whether or not the above method succeeded for the given n.
out = for n from 5 to 7 list(

  R = qRing n;
  J = sunletIdeal(n, R);

  {n, attemptPrimeDescent(J)}
  )
