module Data.Ratio

infix 10 //

export
record Ratio a where
  constructor MkRatio
  nm, dn : a

public export
Rational : Type
Rational = Ratio Integer


gcd : (Eq a, Integral a) => a -> a -> a
gcd x y =
  if x == 0 then y
  else if y == 0 then x
  else gcd y (x `mod` y)

export
reduce : (Eq a, Integral a) => Ratio a -> Ratio a
reduce (MkRatio n d) =
  let g = gcd n d in MkRatio (n `div` g) (d `div` g)


export partial
(//) : (Eq a, Integral a) => a -> a -> Ratio a
n // d = case d /= 0 of
            True => reduce $ MkRatio n d


namespace Ratio
  export %inline
  numer : Ratio a -> a
  numer = nm

  export %inline
  (.numer) : Ratio a -> a
  (.numer) = nm

  export %inline
  denom : Ratio a -> a
  denom = dn

  export %inline
  (.denom) : Ratio a -> a
  (.denom) = dn


export
Eq a => Eq (Ratio a) where
  MkRatio n d == MkRatio m b = n == m && d == b

export
(Ord a, Num a) => Ord (Ratio a) where
  compare (MkRatio n d) (MkRatio m b) =
    flipIfNeg (b*d) $ compare (n*b) (m*d)
    where
      flipIfNeg : a -> Ordering -> Ordering
      flipIfNeg x EQ = EQ
      flipIfNeg x LT = if x >= 0 then LT else GT
      flipIfNeg x GT = if x >= 0 then GT else LT

export
Show a => Show (Ratio a) where
  showPrec p (MkRatio n d) =
    let p' = User 10
    in  showParens (p >= p') (showPrec p' n ++ " // " ++ showPrec p' d)

export
(Eq a, Integral a) => Num (Ratio a) where
  MkRatio n d + MkRatio m b = reduce $ MkRatio (n*b + m*d) (d*b)
  MkRatio n d * MkRatio m b = reduce $ MkRatio (n*m) (d*b)
  fromInteger x = MkRatio (fromInteger x) 1

export
(Eq a, Integral a, Neg a) => Neg (Ratio a) where
  negate (MkRatio n d) = MkRatio (-n) d
  MkRatio n d - MkRatio m b = reduce $ MkRatio (n*b - m*d) (d*b)

export
(Eq a, Integral a, Abs a) => Abs (Ratio a) where
  abs (MkRatio n d) = MkRatio (abs n) (abs d)

export
(Eq a, Integral a) => Fractional (Ratio a) where
  recip (MkRatio n d) = case n /= 0 of True => MkRatio d n
  MkRatio n d / MkRatio m b = case m /= 0 of
    True => reduce $ MkRatio (n*b) (m*d)
