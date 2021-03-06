# idris2-prim: Axioms and Propositions for Primitive Types in Idris2

This library is to a large degree based on ideas and techniques
first presented by G. Allais (@gallais) in the Idris2 *contrib*
package. It provides axioms and derived laws for working with
primitive types and functions in Idris2. This should make
it possible for client code to *refine* primitive values
(for instance, by means of `Data.DPair.Subset`) and have the
ability to convert between such refined values.
It also should allow us to safely use primitives in recursive
functions.

There is a small [tutorial](src/Documentation.md) explaining
some of the things possible with this library.

## Total Order

All primitives with the exception of `Double` and `%World`
come with a total order `<`, so that the following axioms
hold:

* For all `x`, `y`, exactly one of `x < y`, `x === y`, or
  `x > y` holds.
* `<` is transitive.

Module `Data.Prim.Ord` provides interface `Total`, which encapsulates
these axioms. In addition, it comes with dozens of corollaries following
from the axioms.

## Commutative Rings

All primitive integrals come with operations for addition,
negation, and multiplication, which together form a commutative
ring so that the following axioms hold:

* Addition is commutative and associative.
* `0` is the neutral element of addition.
* `negate x` is the additive inverse of `x`.
* `x - y` is equivalent to `x + negate y`.
* Multiplication is commutative and associative.
* `1` is the neutral element of multiplication.
* Multiplication is distributive with respect to addition.

Module `Data.Prim.Ring` provides interface `RingLaws`, which encapsulates
these axioms. In addition, many corollaries following from the axioms are
provided.

## Supported Idris Versions

The latest commit is daily tested to build against the current
HEAD of the Idris compiler. Since Idris2 releases are happening
rather infrequently at the moment, it is suggested to use
a package manager like [pack](https://github.com/stefan-hoeck/idris2-pack)
to install and maintain matching versions of the Idris compiler
and this library. Pack will also automatically install all
required dependencies.
