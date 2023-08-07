module Data.IntegralGCD

%default total


||| An interface for integer types that it is possible to take the GCD
||| (greatest common denominator) of.
|||
||| This interface exists for totality purposes: Euclid's algorithm is
||| possible to implement for any type that satisfies `Integral`, but it
||| is not provably total unless that implementation satisfies some properties.
|||
||| Implementing this interface asserts to the compiler that Euclid's algorithm
||| is total on this type.
public export
interface (Eq a, Integral a) => IntegralGCD a where
  gcd : a -> a -> a
  gcd x y =
    if x == 0 then y
    else if y == 0 then x
    else assert_total $ gcd y (x `mod` y)


export IntegralGCD Integer where

export IntegralGCD Int where
export IntegralGCD Int8 where
export IntegralGCD Int16 where
export IntegralGCD Int32 where
export IntegralGCD Int64 where

export IntegralGCD Bits8 where
export IntegralGCD Bits16 where
export IntegralGCD Bits32 where
export IntegralGCD Bits64 where
