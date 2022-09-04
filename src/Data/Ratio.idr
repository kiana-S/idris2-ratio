module Data.Ratio

infix 10 //

||| Ratio types, represented by a numerator and denominator of type `a`.
|||
||| Most numeric operations require an instance `Integral a` in order to
||| simplify the returned ratio and reduce storage space.
export
record Ratio a where
  constructor MkRatio
  nm, dn : a

||| Rational numbers, represented as a ratio between
||| two arbitrary-precision integers.
|||
||| Rationals can be constructed using `//`.
public export
Rational : Type
Rational = Ratio Integer


-- This function is almost always total; after all, it's a fairly standard
-- implementation of Euclid's algorithm. Unfortunately, we can't _guarantee_
-- it's total without knowing exactly what the implementation of `Integral a` is,
-- so using an `assert_total` here would be potentially unsafe. The only option
-- is to mark this function, and by extention `reduce`, as non-total.
gcd : (Eq a, Integral a) => a -> a -> a
gcd x y =
  if x == 0 then y
  else if y == 0 then x
  else gcd y (x `mod` y)

||| Reduce a ratio by dividing both components by their common factor. Most
||| operations automatically reduce the returned ratio, so explicitly calling
||| this function is usually unnecessary.
export
reduce : (Eq a, Integral a) => Ratio a -> Ratio a
reduce (MkRatio n d) =
  let g = gcd n d in MkRatio (n `div` g) (d `div` g)


||| Construct a ratio of two values.
export partial
(//) : (Eq a, Integral a) => a -> a -> Ratio a
n // d = case d /= 0 of
            True => reduce $ MkRatio n d


namespace Ratio
  ||| Return the numerator of the fraction in reduced form.
  export %inline
  numer : Ratio a -> a
  numer = nm

  ||| Return the numerator of the fraction in reduced form.
  export %inline
  (.numer) : Ratio a -> a
  (.numer) = nm

  ||| Return the denominator of the fraction in reduced form.
  ||| This value is guaranteed to always be positive.
  export %inline
  denom : Ratio a -> a
  denom = dn

  ||| Return the denominator of the fraction in reduced form.
  ||| This value is guaranteed to always be positive.
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
