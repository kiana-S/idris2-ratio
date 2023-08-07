module Data.Ratio

import Data.Maybe
import Data.So
import Data.IntegralGCD

%default total


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


||| Reduce a ratio by dividing both components by their common factor. Most
||| operations automatically reduce the returned ratio, so explicitly calling
||| this function is usually unnecessary.
export
reduce : IntegralGCD a => Ratio a -> Ratio a
reduce (MkRatio n d) =
  let g = gcd n d in MkRatio (n `div` g) (d `div` g)


||| Construct a ratio of two values, returning `Nothing` if the denominator is
||| zero.
export
mkRatioMaybe : IntegralGCD a => (n, d : a) -> Maybe (Ratio a)
mkRatioMaybe n d = toMaybe (d /= 0) (reduce $ MkRatio n d)

||| Create a ratio of two values.
export partial
mkRatio : IntegralGCD a => (n, d : a) -> Ratio a
mkRatio n d = case d /= 0 of
  True => reduce $ MkRatio n d

||| Create a ratio of two values, unsafely assuming that they are coprime and
||| the denomindator is non-zero.
||| WARNING: This function will behave erratically and may crash your program
||| if these conditions are not met!
export %unsafe
unsafeMkRatio : (n, d : a) -> Ratio a
unsafeMkRatio = MkRatio


infix 9 //

||| Construct a ratio of two values.
export
(//) : IntegralGCD a => (n, d : a) -> {auto 0 ok : So (d /= 0)} -> Ratio a
(//) n d = reduce $ MkRatio n d


||| Round a ratio down to a positive integer.
export
floor : Integral a => Ratio a -> a
floor (MkRatio n d) = n `div` d


namespace Ratio
  ||| Return the numerator of the ratio in reduced form.
  export %inline
  numer : Ratio a -> a
  numer = nm

  ||| Return the numerator of the ratio in reduced form.
  export %inline
  (.numer) : Ratio a -> a
  (.numer) = nm

  ||| Return the denominator of the ratio in reduced form.
  ||| This value is guaranteed to always be positive.
  export %inline
  denom : Ratio a -> a
  denom = dn

  ||| Return the denominator of the ratio in reduced form.
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
IntegralGCD a => Num (Ratio a) where
  MkRatio n d + MkRatio m b = reduce $ MkRatio (n*b + m*d) (d*b)
  MkRatio n d * MkRatio m b = reduce $ MkRatio (n*m) (d*b)
  fromInteger x = MkRatio (fromInteger x) 1

export
(IntegralGCD a, Neg a) => Neg (Ratio a) where
  negate (MkRatio n d) = MkRatio (-n) d
  MkRatio n d - MkRatio m b = reduce $ MkRatio (n*b - m*d) (d*b)

export
(IntegralGCD a, Abs a) => Abs (Ratio a) where
  abs (MkRatio n d) = MkRatio (abs n) (abs d)

export
IntegralGCD a => Fractional (Ratio a) where
  recip (MkRatio n d) = case n /= 0 of True => MkRatio d n
  MkRatio n d / MkRatio m b = case m /= 0 of
    True => reduce $ MkRatio (n*b) (m*d)
