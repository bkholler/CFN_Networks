-- Creates the set of indices for the ring of Fourier coordinates
indexSet = n -> toList delete(null, apply(toList(n:0)..toList(n:1), i ->  if sum(i) % 2 == 0 then i));

-- Creates the ring of Fourier coordinates
qRing = n -> QQ[apply(indexSet(n), g -> q_g)];

-- Creates the parameterization of the sunlet network variety in the Fourier parameters
-- Returns the binomials parameterizing the network as list corresponding to variables
-- q_g in lexicographic order as shown in Equation 3
sunletParam = n -> (

  indR := indexSet n;

  S := QQ[{t} | apply(2*n, i -> a_i)];

  --network param
  images := for ivec in indR list (

    product(apply(n, j -> if ivec_j == 1 then a_j else t))*(product(apply(n-1, j -> if odd sum(ivec_(toList(0..j))) then a_(n+j) else t)) + product(apply(toList(1..n-1), j -> if odd sum(ivec_(toList(1..j))) then a_(n+j) else t)))
    );

  return images;
  )

-- Creates the parameterization of the sunlet network variety in the Fourier coordinates
-- Note that we give each q_g variable degree 2n so that the elimination ideal is properly homogenized
-- This greatly speeds up the Grobner basis computation and also allows us to compute a degree-bounded Grobner basis with degLimit option
-- Note that degLimit should just be the degree that one wants the resulting polynomials in the q_g to be if each q_g has degree 1
sunletElimIdeal = {degLimit => null, Qring => null} >> opts -> n -> (

  indR := indexSet n;

  S := QQ[{t} | apply(2*n, i -> a_i) | apply(indR, i -> q_i), Degrees =>  toList(2*n+1 : 1)|toList(2^(n-1) : 2*n - 1), MonomialOrder => {2*n+1, 2^(n-1)}];

  --network param
  images := for ivec in indR list (

    product(apply(n, j -> if ivec_j == 1 then a_j else t))*(product(apply(n-1, j -> if odd sum(ivec_(toList(0..j))) then a_(n+j) else t)) + product(apply(toList(1..n-1), j -> if odd sum(ivec_(toList(1..j))) then a_(n+j) else t)))
    );

  elimIdeal := ideal(for i from 0 to #images-1 list q_(indR#i) - images#i);
  G := selectInSubring(1, if opts.degLimit === null then gens gb(elimIdeal) else gens gb(elimIdeal, DegreeLimit => 2*n*(opts.degLimit)));
  R := if opts.Qring === null then qRing n else opts.Qring;
  return(sub(ideal G, R));
  )


-- Creates an index g from the colors cE and cO as described in the proof of Proposition 4.7
indexFromColors = (n, cE, cO) -> (

  c := toList(1..(n-2)) / (i -> if i % 2 == 1 then cE#(i//2) else cO#(i//2-1));
  c = {0} | c | {0};

  return {0}| (toList(1..(n-1)) / (i -> (c#i + c#(i-1)) % 2));
  )

-- creates a new index, gLift, such that gLift|_F = a and gLift|_{[n]\F} = g
interleave = (g, F, a) -> (

  gLift := g;

  for i from 0 to #F - 1 do(

    gLift = insert(F#i, a#i, gLift);
    );

  return gLift;
  );

-- Finds a basis for the empty glove G(n, \emptyset) of the sunlet network for even n. Returns this basis as a list {L_c}_{c is a valid coloring} where each L_c = {g_1, g_2, g_3, g_4}
-- represents a polynomial of the form f_c as described in Proposition 4.8.
emptyGlove = n -> (

  if n % 2 == 1 then error("The empty glove is only valid for even n");

  m := (n-2) // 2;

  C := flatten for cE in drop(toList(toList(m:0)..toList(m:1)), 1) list for cO in drop(toList(toList(m:0)..toList(m:1)), 1) list cE|cO;

  return apply(C, c -> {indexFromColors(n, toList(m:0), toList(m:0)), indexFromColors(n, take(c, m),toList(m:0)),
    indexFromColors(n, take(c, m), take(c, -m)), indexFromColors(n, toList(m:0), take(c, -m))});
  )

-- Finds a basis for the glove G(n, F, a) of the sunlet network. Does this by finding a basis for the empty glove G(n-#F, \emptyset)
-- using the emptyGlove method and then lifts this to a basis of G(n, F, a) as described in Proposition 4.7.
-- The basis is returned in the same format that the basis for emptyGlove is returned
glove = {emptyG => null} >> opts -> (n, F, a) -> (

  G := if opts.emptyG === null then emptyGlove(n - #F) else opts.emptyG;

  if even sum(a) then return G / (i -> (i / (g -> interleave(g, F, a)))) else return G / (i -> (i / (g -> interleave((g + (toList(#g-1:0)|{1})) % 2, F, a))))
  )

-- Given an index g with g|_F = a, makes the complementary index h such that h|_F = a and h|_{[n]\F} = g|_{[n]\F}+(1,...,1) % 2
-- as described in Definition 4.2.
makeH = (n, g, F, a) -> (

  if #F > 0 then(

    notF := toList(set(0..(n-1)) - set(F));

    return interleave(apply(g_notF, i -> (i + 1) % 2), F, a);
    )

  else(

    return (g + toList(#g:1))%2;
    );
  )

-- Turns a set of indices L_c = {g_1, g_2, g_3, g_4} into the polynomial f_c
-- as described in Proposition 4.8.
makePoly = (n, L, F, a, R) -> (

  hL := L / (g -> makeH(n, g, F, a));

  return sum(for i from 0 to 3 list (-1_R)^(i)*((q_(L_i))_R)*((q_(hL_i))_R));
  )

-- Finds the binomials in the sunlet network ideal by lifting the
-- binomials that vanish on the underlying trees as described in Remark 4.6
sunletBinomials = (n, R) -> (

  splits := for i from 0 to n-5 list toList(0..(i+1));

  polys :=
  for A in splits list(

    B := toList(set(0..(n-2)) - set(A));

    indA := indexSet(#A);
    indB := indexSet(#B);

    M0 := minors(2, matrix for a in indA list for b in indB list (q_({0}|a|b))_R);

    indA = toList delete(null, apply(toList(#A:0)..toList(#A:1), i ->  if sum(i) % 2 == 1 then i));
    indB = toList delete(null, apply(toList(#B:0)..toList(#B:1), i ->  if sum(i) % 2 == 1 then i));

    M1 := minors(2, matrix for a in indA list for b in indB list (q_({0}|a|b))_R);

    M0+M1
    );

  return sum(polys);
  )

-- Computes the sunlet ideal by finding the polynomials for each glove
-- and adding the binomials
sunletQuadIdeal = (n, R) -> (

  fourTerms :=
  for m from 4 to n-1 list(
    if odd m then continue;

      emptG := emptyGlove(m);

      for F in subsets(toList(0..n-1), n-m) list(

        if F_0 == 0 then (

          for a in toList(toList(n-m-1:0)..toList(n-m-1:1)) list(

            --print((F,a));
            apply(glove(n, F, {1}|a, emptyG => emptG), L -> makePoly(n, L, F, {1}|a, R))
            )
          )
        else (
          for a in toList(toList(n-m:0)..toList(n-m:1)) list(

            --print((F,a));
            apply(glove(n, F, a, emptyG => emptG), L -> makePoly(n, L, F, a, R))
            )
          )
        )
    );

  fourTerms = flatten(flatten(flatten(fourTerms)));

  fourTerms = if even n then  fourTerms | (emptyGlove(n) / (L -> makePoly(n, L, {}, {}, R))) else fourTerms;


  return ideal(fourTerms) + sunletBinomials(n, R);
  );

n = 5
d = 2
R = qRing n
I = sunletQuadIdeal(n, R)
psi = sunletParam n;
J = sunletElimIdeal(n, Qring => R, degLimit => d)
