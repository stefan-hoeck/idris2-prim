# idris2-prim: Axioms and Propositions for Primitive Types in Idris2

This library is to a large degree based on ideas and techniques
first presented by G. Allais (@gallais) in the Idris2 *contrib*
package. It provides axioms and derived laws for working with
primitive types and functions in Idris2. This should make
it possible for client code to *refine* primitive values
(for instance, by means of `Data.DPair.Subset`) and have the
ability to convert between such refined values.

Right now, this is still work in progress.
