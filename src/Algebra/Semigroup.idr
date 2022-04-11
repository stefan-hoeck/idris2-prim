module Algebra.Semigroup

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a semigroup hold: `(<+>)` is associative.
|||
||| Note: If the type is actually a monoid, use `Data.Algebra.LMonoid` instead.
public export
interface Semigroup a => LSemigroup a where
  0 appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z

||| This interface is a witness that for a
||| type `a` the axioms of a commutative semigroup hold:
||| `(<+>)` is commutative.
public export
interface LSemigroup a => CommutativeSemigroup a where
  0 appendCommutative : {x,y : a} -> x <+> y === y <+> x
