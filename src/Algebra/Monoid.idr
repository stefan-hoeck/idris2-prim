module Algebra.Monoid

import Data.List

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a monoid hold: `(<+>)` is associative
||| with `neutral` being the neutral element.
public export
interface Monoid a => LMonoid a where
  0 appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z

  0 appendLeftNeutral : {x : a} -> Prelude.neutral <+> x === x

  0 appendRightNeutral : {x : a} -> x <+> Prelude.neutral === x

export
LMonoid (List a) where
  appendAssociative = Data.List.appendAssociative _ _ _
  appendRightNeutral = appendNilRightNeutral _
  appendLeftNeutral = Refl

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
LMonoid String where
  appendAssociative = unsafeRefl
  appendRightNeutral = unsafeRefl
  appendLeftNeutral = unsafeRefl

||| This interface is a witness that for a
||| type `a` the axioms of a commutative monoid hold:
||| `(<+>)` is commutative.
public export
interface LMonoid a => CommutativeMonoid a where
  0 appendCommutative : {x,y : a} -> x <+> y === y <+> x
