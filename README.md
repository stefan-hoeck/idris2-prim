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

## Supported Idris Versions
At the moment, this library is being developed against
the current main branch of the Idris2 project.
The latest commit has been built against Idris 2 of version the
set in the ``.idris-version`` file. This file contains a version in
the format which ``git describe --tags`` gives.
