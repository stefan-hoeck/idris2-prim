# Documentation and Examples

This is a literal Idris file, so we first need some
imports:

```idris
module Documentation

import Data.Prim.Bits64

%default total
```

At the moment, the main focus of this library lies on the
strict total order of most primitive types (with the exception
of `%World` and `Double`). For every primitive type, a
relation `(<)` is defined, with `m < n` being
a witness that `m` is strictly smaller than `n`. From this, we
can define the following aliases:

* `m > n = n < m`
* `m <= n = Either (m < n) (m === n)`
* `m >= n = n <= m`
* `m /= n = Either (m < n) (m > n)`

For these relations we implement interface `Data.Prim.Ord.Strict`,
which comes with four axioms we assume (but can't proof in Idris) to hold
for the ordered primitive types:

1. `<` is transitive: From `k < m` and `m < n` follows `k < n`.
2. Trichotomy: For all values `m,n` of the given type, exactly
   one of `m < n`, `m === n`, or `m > n` holds.

Module `Data.Prim.Ord` comes with many corollaries following
from the axioms listed above. We will use these when manually
calculating new proofs from existing ones.

## Use Case 1: Safe Division

As a first example, we want to implement safe integer
division for `Bits64`. In order to do so, we need an
erased proof that the denominator is strictly positive.

```idris
safeDiv : (n,d : Bits64) -> (0 prf : 0 < d) => Bits64
safeDiv n d = n `div` d
```

We can conveniently invoke `safeDiv` with denominators
known at compile time:

```idris
half : Bits64 -> Bits64
half n = n `safeDiv` 2

ten : Bits64
ten = safeDiv 100 10
```

If, however, the denominator is only known at runtime,
we first need to *refine* it. For this, we introduce
a new type for strictly positive values of type `Bits64`:

```idris
0 Positive : Type
Positive = Subset Bits64 (> 0)
```

It is convenient to be able to use integer literals with
values of type `Positive`. Although the constructors of `(<)`
and similar predicates are not publicly exported (for safety
reasons, see below), we can still use proof search to create
values of type `(<)` automatically if both arguments are known
at compile time, because function `mkLT`, which can be used
to manually define values of type `(<)`, is annotated with
a `%hint` pragma.

```idris
fromInteger :  (n : Integer)
            -> (0 prf : cast n > the Bits64 0)
            => Positive
fromInteger n = Element (cast n) prf

twelve : Positive
twelve = 12
```

We can use `trichotomy` (or `Bits64.comp`) to refine
values only known at runtime. This returns a value of
type `Trichotomy (<) (==) m n`, which holds erased
proofs that exactly one of the following holds:
`m < n`, `m > n`, or `m == n`:

```idris
positive : Bits64 -> Maybe Positive
positive x = case trichotomy 0 x of
  LT y _ _ => Just (Element x y)
  EQ _ _ _ => Nothing
  GT _ _ _ => Nothing
```

## Use Case 2: Converting Values to Strings

A more interesting use case is the modulo operation. It comes
with the postcondition that if the modulus is positive (the
function's precondition), the result will be strictly smaller
than the modulus. The unsigned integer modules export functions `rmod`
encapsulating this behavior.

We will implement a small function for converting an
integer to a string in a given base. We accept
bases in the range `[2,16]`:

```idris
record Base where
  constructor MkBase
  value : Bits64
  0 gt1   : value > 1
  0 lte16 : value <= 16

namespace Base
  public export
  fromInteger :  (n : Integer)
              -> (0 gt1   : cast n > the Bits64 1)
              => (0 lte16 : cast n <= the Bits64 16)
              => Base
  fromInteger n = MkBase (cast n) gt1 lte16
```

To convert a digit to a hexadecimal character,
we require the digit to be strictly smaller
than sixteen as a precondition:

```idris
hexChar : (d : Bits64) -> (0 prf : d < 16) => Char
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
lit : Bits64 -> Base -> String
lit 0 _ = "0"
lit x (MkBase b gt1 lte16) = go [] x
  where go : List Char -> Bits64 -> String
        go cs 0 = pack cs
        go cs v =
          let 0 gt0         = the (0 < b) $ trans %search gt1
              Element d ltb = rmod v b
              v2            = sdiv v b
              c             = hexChar d {prf = trans_LT_LTE ltb lte16}
           in go (c :: cs) (assert_smaller v v2)
```

Functions `rmod` and `sdiv` each require a proof that `b` is larger than zero.
We can construct such a proof from the transitivity of `(<)`: We know that
`b > 1` (value `gt1`), and Idris can figure out on its own that `0 < 1`
(invocation of `%search`). Passing both arguments to `LT.trans` generates
the desired proof. Since this is used twice (in `rmod` and `sdiv`),
I bound it to erased local variable `gt0`.

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

There are several techniques for making such code more concise.
First, we can be clever when choosing our constraints: In `Base` we
stored the lower bound as `b > 1` instead of `b >= 2`. We could also
store additional derived proofs in the `Base` data type. Since they
have zero quantity, they will be erased and have no effect on the runtime
behavior of our application.
We can also try to come up with some custom hints local to our source
files. Here is an example that allows us to get rid of manual proof
passing:

```idris
%hint
0 gt0 : n > 1 -> n > 0
gt0 gt = trans (the (0 < 1) %search) gt

%hint
0 lt16 : m < n -> n <= 16 -> m < 16
lt16 = trans_LT_LTE

lit2 : Bits64 -> Base -> String
lit2 0 _ = "0"
lit2 x (MkBase b geq2 lte16) = go [] x
  where go : List Char -> Bits64 -> String
        go cs 0 = pack cs
        go cs v =
          let Element d ltb = rmod v b
           in go (hexChar d :: cs) (assert_smaller v $ sdiv v b)
```

That looks pretty nice. The only ugly (and unsafe!) piece is the
call to `assert_smaller`, which is needed to satisfy the totality
checker. Alas, there is no way getting rid of that one.

## Use Case 3: Well-founded Recursion

Or is there? What we need is a thing called *well-founded recursion*,
based on the concept of [*well-founded relations*](https://en.wikipedia.org/wiki/Well-founded_relation).
A relation `<` on a set `X` is well founded, if every non-empty subset `S`
of `X` contains a minimal element with respect to `<`, that is, an element
`m`, so that there is no `s` in `S` with `s < m`.

This can also be stated like so: For every `x` in `X`, any chain
`x1,x2,...xn` of values with `x1 < x2 < ... xn < x` must be finite.
Otherwise, such a chain would be a non-empty subset of `X` with no
minimal element.

A data type encapsulating these concepts can be found in module
`Control.WellFounded` in the *base* library. There is data type
`Accessible rel x`, a value of which is a proof that every chain
of values related via `rel` and starting from `x` will be finite.
We can construct a value of this type using recursion, but we must make
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

Here is how to do this for `Bits64` and `(<)`:

```idris
lit3 : Bits64 -> Base -> String
lit3 0 _ = "0"
lit3 x (MkBase b _ _) = go [] x (accessLT x)
  where go : List Char -> (n : Bits64) -> (0 _ : Accessible (<) n) -> String
        go cs n (Access rec) = case comp 0 n of
          LT ngt0 _ _ =>
            let Element d  _   = n `rmod` b
                Element n2 ltn = n `rdiv` b
             in go (hexChar d :: cs) n2 (rec n2 ltn)
          EQ _    _ _   => pack cs
          GT _    _ lt0 => void (Not_LT_MinBits64 lt0)
```

Note, how we used `comp` to compare the current value against the
lower bound (which could be any number of type `Bits64`). This
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
somewhere: `Bits64` is a primitive after all. Indeed, this was
used in the implementation of `accessLT`, which we used to
create the initial proof of accessibility.

## Implementation Details

Since we are working with primitives, all axioms must be
assumed to hold on all backends, and all values proofing
such axioms must be magically crafted using unsafe primitives
like `believe_me` or `assert_total`. But this means, we have to
be careful when using such proofs during type checking. It's best
to explain the problem at hand in the words of @gallais, who
first came up with a set of laws on the ordering of `Int` in
the *contrib* library:

> The type `Int` is a primitive type in Idris. The only handle we have on
> it is provided by built-in functions. This is what we are going to use
> to define relations on Int values. For instance, we will declare that
> `a` is strictly less than `b` whenever `a < b` is provably equal to `True`.
>
> These built-in functions only reduce on literals. This means we will not
> be able to rely on their computational behaviour to prove statements in
> open contexts.
>
> For instance, no amount of pattern-matching will help us prove:
> `LT_not_EQ : LT a b -> Not (EQ a b)`
>
> Our solution in this file is to use unsafe primitives to manufacture such
> proofs. This means we are going to essentially postulate some *conditional*
> results. We do not want such conditional results to reduce to canonical
> forms too eagerly.
>
> Indeed the statement `GT 0 1 -> EQ 0 1` should be provable because 0 is not
> greater than 1. But its proof should not reduce to a constant function
> returning the value `Refl` because it is not true that `0` and `1` can be
> unified. If the proof were to behave this way, we could, in an absurd context,
> coerce values from any type to any other and cause segmentation faults.
>
> Our solution is to be extremely wary of proofs that are passed to us
> and to only consider returning a magically-crafted output if we have
> managed to observe that the input is itself in canonical form i.e. to
> have evaluation stuck on open terms.
>
> This is the purpose of the `strictX : X -> Lazy c -> c` functions defined in
> this file. They all will be waiting until their first argument is in canonical
> form before returning their second.

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
