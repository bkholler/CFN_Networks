load "sunletQuadGens.m2"
needsPackage "Tropical"
needsPackage "Normaliz"

-- This command computes the tropical variety F of I using the Tropical package
-- The cones of F correspond to binomial initial ideals of I
-- It then checks which of these ideals are prime and thus toric
-- It returns the tropical variety F and a list
primeCones = I -> (
    G := flatten entries gens gb I;
    F := tropicalVariety(I);
    r := rays(F);
    c := maxCones(F);
    cones := for i in c list (r_i);
    weights := cones / (c -> interiorVector(coneFromVData(c))) / (w -> flatten entries transpose w);
    L := {};
    for i from 0 to  #weights-1 do (
      temp = gfanInitialForms(G, -weights#i, "ideal" => true);
  	  if isBinomial(ideal(temp)) then (
        if binomialIsPrime(ideal(temp)) then L = append(L, (ideal(temp), cones#i, c#i));
        );
  	  );
    return (F , delete(null, L));
    );

-- This command computes the normal toric degenerations of I
-- it first uses primeConesOfIdeal to find the cones in the tropical variety that give toric initial ideals
-- It then checks which of the toric varieties are normal using normaliz
normalPrimes = I -> (

  np := {};

  (F, pc) := primeCones I;

  for l in pc do(

    (J, C, indC) := l;

    ls = linealitySpace F;

    A := C | ls | -ls;

    normA := normaliz(A, "normalization");

    isANormal := normA#"inv"#"integrally closed";

    if isANormal then np = append(np, transpose(A));

    );

  return (F, pc, np);
  )

-- Make the ideal I_5 using our quadratic generators
n = 5;
R = qRing n;
I = sunletQuadIdeal(n, R)

-- Check that I is prime and of the correct dimension
dim10 = (rank jacobian matrix {sunletParam n} == 10);
primeI = isPrime I;

-- this computation takes a few minutes
-- To run the full computation simply uncomment the line below
-- Our example below is the last toric degeneration in the list pc
-- (F, pc, np) = normalPrimes I;

-- This is the toric degeneration described in Example 5.4
K =  ideal {q_{0, 0, 1, 1, 0}*q_{0, 1, 0, 0, 1}-q_{0, 0, 1, 0, 1}*q_{0, 1, 0, 1, 0}, q_{0, 0, 1, 0, 1}*q_{1, 1, 0, 1, 1}-q_{0, 0, 0, 1,
     1}*q_{1, 1, 1, 0, 1}, q_{0, 0, 1, 0, 1}*q_{1, 1, 0, 0, 0}-q_{0, 0, 0, 0, 0}*q_{1, 1, 1, 0, 1}, q_{0, 1, 1, 1, 1}*q_{1, 0, 1, 0,
     0}-q_{0, 1, 1, 0, 0}*q_{1, 0, 1, 1, 1}, q_{0, 1, 1, 1, 1}*q_{1, 0, 0, 1, 0}-q_{0, 0, 0, 1, 1}*q_{1, 1, 1, 1, 0}, q_{0, 1, 1, 0,
     0}*q_{1, 0, 0, 1, 0}-q_{0, 0, 0, 0, 0}*q_{1, 1, 1, 1, 0}, q_{1, 0, 1, 1, 1}*q_{1, 1, 0, 0, 0}-q_{1, 0, 1, 0, 0}*q_{1, 1, 0, 1,
     1}, q_{0, 1, 1, 1, 1}*q_{1, 1, 0, 0, 0}-q_{0, 1, 1, 0, 0}*q_{1, 1, 0, 1, 1}, q_{0, 0, 0, 1, 1}*q_{1, 0, 1, 0, 0}-q_{0, 0, 0, 0,
     0}*q_{1, 0, 1, 1, 1}, q_{0, 0, 0, 1, 1}*q_{0, 1, 1, 0, 0}-q_{0, 0, 0, 0, 0}*q_{0, 1, 1, 1, 1}, q_{0, 0, 0, 1, 1}*q_{1, 1, 0, 0,
     0}-q_{0, 0, 0, 0, 0}*q_{1, 1, 0, 1, 1}}


-- The A-matrix whose columns give monomials parameterizing the toric variety above is
A =  matrix {{-1, -1, 0, 0, 2, 2, -1, -1, 0, 0, 1, 1, -1, -1, 0, 0}, {-1, -1, 0, 2, 0, 2, -1, -1, 1, -1, 0, 0, 0, 0, 1, -1}, {-1,
     -1, -1, 1, -1, 1, 1, 1, 5, -1, -1, -1, -1, -1, -1, 1}, {-1, -1, 1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, -1, 1, 1}, {1, 1, 1, 1,
     1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0}, {1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0}, {2, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1,
     0, 0, 0}, {-1, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, 1, 0, 0}, {-1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0}, {-1,
     -1, -1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1}, {-1, -1, -1, -1, -1, -1, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0}, {-1, -1, -1, -1, 0,
     0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 0}, {-2, -1, -1, -1, -1, -1, -1, 0, -1, -1, -1, 0, -1, 0, 0, 0}, {1, 0, 1, 1, 0, 0, 1, 0, 0,
     0, 1, 0, 0, -1, 0, 0}, {1, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0}, {1, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1}}


-- The output from normaliz below shows that K is normal and Gorenstein
normA = normaliz(transpose(A), "normalization")


-- To check that the toric variety is Gorenstein we verify that the canonical module of CC[NN A] has one generator
-- This is done by ensuring every interior lattice point in the fundamental parallelepiped of C = cone(A) also lies in the polyhedron P
-- that is obtained by shifting C by this single generator described in Section 5.2
C = coneFromVData(A)
P = convexHull(transpose matrix {{2, 2, 4, 2, 2, 3, 4, -1, -1, -1, -2, -3, -4, 1, 1, 1}}) + C

-- This finds all interior lattice points we need to consider
interiorPts = for S in toList(toList(16:0)..toList(16:1)) list(

  if inInterior(A*(transpose matrix {S}), C) then A*(transpose matrix {S})
  )

interiorPts = delete(null, interiorPts)

-- This checks every lattice point under consideration lies in P
isGorenstein = all(interiorPts,  v -> contains(P, convexHull({v})))
