load "sunletQuadGens.m2"

-- compute dimensions of small sunlets symbolically
-- since we are computing symbolically this gives a proof that
-- the sunlet variety for n = 5 to n = 8 has dimension 2n
smallSunletDims = for n from 5 to 8 list {n, rank jacobian matrix {sunletParam n}}

-- compute dimensions of small sunlets at a random point
-- with probability one this is the dimension of the variety
-- we've run this several times and the dimension is always 2n
big = for n from 9 to 17 list(

  J = jacobian matrix {sunletParam n};

  vals = matrix{apply(#support(J), i -> random(QQ))};

  {n, rank(sub(J, vals))}
  )
