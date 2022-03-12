# Documentation and Examples

This is a literal Idris file, so we first need some
imports:

```idris
module Documentation

import Data.DPair
import Data.Prim

%default total
```

## Use Case 1: Safe Division

As a first example, we want to implement safe integer
division for `Bits8`. In order to do so, we need an
erased proof that the denominator is strictly positive.

```idris
safeDiv : (m,n : Bits8) -> (0 _ : 0 < n) => Bits8
safeDiv m n = m `div` n
```

We can conveniently invoke `safeDiv` with denominators
known at compile time:

```idris
half : Bits8 -> Bits8
half n = n `safeDiv` 2

ten : Bits8
ten = safeDiv 100 10
```

If, however, the denominator is only known at runtime,
we first need to *refine* it. For this, we introduce
a new type for strictly positive values of type `Bits8`:

```idris
0 Positive : Type
Positive = Subset Bits8 (> 0)
```

It is convenient to be able to use integer literals with
values of type `Positive`. Although the constructors of `(<)`
and similar predicates are not publicly exported (for safety
reasons, see below), we can still use proof search to create
values of `(<)` automatically if both arguments are known
at compile time, because function `lt`, which can be used
to manually define values of type `(<)`, is annotated with
a `%hint` pragma.

```idris
fromInteger :  (n : Integer)
            -> (0 prf : the Bits8 0 < cast n)
            => Positive
fromInteger n = Element (cast n) prf

twelve : Positive
twelve = 12
```

We can use `LT.decide` to refine values only known at
runtime. This returns a value of type `Dec0`, which
is like `Dec` but with erased values wrapped in the
constructors.

```idris
positive : Bits8 -> Maybe Positive
positive x = case LT.decide 0 x of
  Yes0 prf => Just $ Element x prf
  No0 _    => Nothing
```

### Converting Values to Strings

A more interesting case is the modulus operation. It comes
with the guarantees that if the modulus is positive, the
result will be strictly smaller than the modulus.
The unsigned integer modules export functions `smod`
encapsulating this behavior.

We will implement a small function for converting an
integer to a string in a given base. We accept
bases in the range `[2,16]`:

```idris
record Base where
  constructor MkBase
  value : Bits8
  0 geq2  : value >= 2
  0 leq16 : value <= 16

namespace Base
  public export
  fromInteger :  (n : Integer)
              -> (0 geq2  : cast n >= the Bits8 2)
              => (0 leq16 : cast n <= the Bits8 16)
              => Base
  fromInteger n = MkBase (cast n) geq2 leq16
```

We can convert a digit to a hexadecimal character.
As a precondition, we require the digit to be strictly smaller
than sixteen:

```idris
hexChar : (d : Bits8) -> (0 prf : d < 16) => Char
hexChar d = case d < 10 of
  True  => cast $ 48 + d
  False => cast $ 87 + d
```

We can now implement a function for converting a value
to a string in the given base. This will require some
manual proof passing: The goal of this library is not
to provide the functionality for Idris to derive all
kinds of proofs automatically. As a result, the implementation
is quite verbose.

```idris
lit : Bits8 -> Base -> String
lit 0 _ = "0"
lit x (MkBase b geq2 leq16) = go [] x
  where go : List Char -> Bits8 -> String
        go cs 0 = pack cs
        go cs v =
          let Element d ltb = smod v b {prf = trans_LT_LTE %search geq2}
              v2            = sdiv v b {prf = trans_LT_LTE %search geq2}
              c             = hexChar d {prf = trans_LT_LTE ltb leq16}
           in go (c :: cs) (assert_smaller v v2)
```

We can give this a go at the REPL:

```repl
Documentation> lit 12 2
"1100"
Documentation> lit 12 3
"110"
Documentation> lit 12 5
"22"
Documentation> lit 12 8
"14"
Documentation> lit 12 16
"c"
```

<!-- vi: filetype=idris2
-->
