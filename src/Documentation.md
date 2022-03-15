# Documentation and Examples

This is a literal Idris file, so we first need some
imports:

```idris
module Documentation

import Data.Prim.Bits8

%default total
```

## Use Case 1: Safe Division

As a first example, we want to implement safe integer
division for `Bits8`. In order to do so, we need an
erased proof that the denominator is strictly positive.

```idris
safeDiv : (m,n : Bits8) -> (0 prf : 0 < n) => Bits8
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
            -> (0 prf : cast n > the Bits8 0)
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
positive x = case trichotomy 0 x of
  LT y f g => Just (Element x y)
  EQ f y g => Nothing
  GT f g y => Nothing
```

## Use Case 2: Converting Values to Strings

A more interesting use case is the modulus operation. It comes
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
  0 gt1   : value > 1
  0 leq16 : value <= 16

namespace Base
  public export
  fromInteger :  (n : Integer)
              -> (0 gt1   : cast n > the Bits8 1)
              => (0 leq16 : cast n <= the Bits8 16)
              => Base
  fromInteger n = MkBase (cast n) gt1 leq16
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
to provide Idris with the functionality to derive all
kinds of proofs automatically. Such a thing would probably
be doomed to fail anyway. As a result, the implementation
is quite verbose.

```idris
lit : Bits8 -> Base -> String
lit 0 _ = "0"
lit x (MkBase b gt1 leq16) = go [] x
  where go : List Char -> Bits8 -> String
        go cs 0 = pack cs
        go cs v =
          let Element d ltb = rmod v b {prf = trans %search gt1}
              v2            = sdiv v b {prf = trans %search gt1}
              c             = hexChar d {prf = trans_LT_LTE ltb leq16}
           in go (c :: cs) (assert_smaller v v2)
```

Functions `rmod` and `sdiv` each require a proof that `b` is larger than zero.
We can construct such a proof from the transitivity of `(<)`: We know that
`b > 1` (value `gt1`), and Idris can figure out on its own that `0 < 1`
(invocation of `%search`). Passing both arguments to `LT.trans` generates
the desired proof.

In addition, `rmod` returns a proof stating that its result
is strictly smaller than the modules. We use this and
the fact that from `k < m` and `m <= n` follows `k < n`
in the call to `hexChar`.

Let's give this a go at the REPL:

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

There are several techniques to make writing such code somewhat easier.
First, we can be clever when choosing our constraints: In `Base` we
stored the lower bound as `b > 1` instead of `b >= 2`. We could also
store additional derived proofs in the `Base` data type. Since they
have zero quantity, the will be erased and have no effect on the runtime
behavior of our application.

We can also try to come up with some custom hints local to our source
files. Here's an example that allows us to get rid of manual proof
passing:

```idris
%hint
0 gt0 : n > 1 -> n > 0
gt0 gt = LT.trans ?foo gt

%hint
0 lt16 : m < n -> n <= 16 -> m < 16
lt16 = trans_LT_LTE

lit2 : Bits8 -> Base -> String
lit2 0 _ = "0"
lit2 x (MkBase b geq2 leq16) = go [] x
  where go : List Char -> Bits8 -> String
        go cs 0 = pack cs
        go cs v =
          let Element d ltb = rmod v b
           in go (hexChar d :: cs) (assert_smaller v $ sdiv v b)
```

That looks pretty nice. The only ugly (and unsafe!) piece is the
call to `assert_smaller`, which is needed to satisfy the totality
checker. Alas, there is no way getting rid of that one.

## Use Case 3: Well-founded Recursion

Or is there? What we need is a concept called *well-founded recursion*,
based on the concept of [*well-founded relations*](https://en.wikipedia.org/wiki/Well-founded_relation).
A relation `<` on a set `X` is well founded, if every non-empty subset `S`
of `X` contains a minimal element with respect to `R`, that is, an element
`m`, so that there is no `s` in `S` with `s < m`.

This can also be stated like so: For every `x` in `X`, any chain
`x1,x2,...xn` of values with `x1 < x2 < ... xn < x` must be finite.
Otherwise, such a chain would be a non-empty subset of `X` with no
minimal element.

Data types encapsulating these concepts can be found in module
`Control.WellFounded` in the *base* library. There is data type
`Accessible rel x`, a value of which is a proof that every chain
of values related via `rel` and starting from `x` will be finite.
We can constructor such a value using recursion, but we must make
sure to proof to Idris that this recursion eventually comes to
an end.

In addition, there is interface `WellFounded a rel`, which allows us
to come up with a value of type `Accessible rel x` for every value
`x` of type `a`.

An (erased) value of type `Accessible rel x` can be used as the
function argument, which will get strictly smaller in every
recursive function call. All we need to do is pass the current
value a proof that the next function argument `y` is related
to `x` via `rel`, that is, `rel y x` does hold.

Here is how to do this for `Bits8` and `(<)`:

```idris
lit3 : Bits8 -> Base -> String
lit3 0 _ = "0"
lit3 x (MkBase b _ _) = go [] x (accessLT x)
  where go : List Char -> (n : Bits8) -> (0 _ : Accessible (<) n) -> String
        go cs n (Access rec) = case comp 0 n of
          LT ngt0 _ _ =>
            let Element d  _   = n `rmod` b
                Element n2 ltn = n `rdiv` b
             in go (hexChar d :: cs) n2 (rec n2 ltn)
          EQ _    _ _   => pack cs
          GT _    _ lt0 => void (Not_LT_MinBits8 lt0)
```

Note, how we used `comp` to compare the current value against the
lower bound (which could be any number of type `Bits8`). This
returns a value of type `Trichotomy (<) (==) 0 n`, which encapsulates
the trichotomy of `<`: Exactly one of the three possibilities
of `m < n`, `m == n`, and `n < m` holds.

Function `rdiv` can be used if `n` is provably greater
than zero (witnessed by value `ngt0`) and `b` is strictly
greater than one. In this case it returns a proof that
its result (`n2`) is strictly smaller than its first argument (`n`).
We pass this proof to function `rec` to get a value of type
`Accessible (<) n2`, which we use as the erased argument in
the recursive function call. Idris know that this must be
strictly smaller than than the previous accessibility proofs,
so the totality checker is satisfied.

Of course, there must be some call to `assert_smaller` hidden
somewhere: `Bits8` is a primitive after all. Indeed, this was
used in the implementation of `accessLT`, which we used to
create the initial proof of accessibility.

## Conclusion

The interfaces and utility functions provided by this library allow
us to get strong guarantees about the validity of our code
when working with primitive data types.

Yet, I'm still experimenting with new additions that might be helpful,
and with different designs to get the best compromise in terms of
code reuse, type inference, and expressiveness.
Therefore, this library is still bound to change in breaking ways.

<!-- vi: filetype=idris2
-->
