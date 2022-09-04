# idris2-ratio

A small library for arbitrary-precision ratio types.

The main type exported by this library is `Data.Ratio.Rational`, which is a
number type stored as the ratio between two integers. The ratio is always stored
in reduced form to save memory space, but this comes at the cost of worst-case
O(n) arithmetic.

The specific integer type used for the ratio can be set by using `Data.Ratio.Ratio`,
which takes a type parameter `a`. Most operations require `Integral a`.
