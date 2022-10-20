module Algebra.Monoid

import Data.List
import public Algebra.Semigroup
import Syntax.PreorderReasoning

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a monoid hold: `(<+>)` is associative
||| with `neutral` being the neutral element.
public export
interface MonoidV a (0 mon : Monoid a) | a where
  constructor MkMonoidV
  0 m_appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z

  0 appendLeftNeutral : {x : a} -> Prelude.neutral <+> x === x

  0 appendRightNeutral : {x : a} -> x <+> Prelude.neutral === x

----------------------------------------------------------------------------------
----          Derived Implementations
----------------------------------------------------------------------------------

public export
monSem : Monoid a -> Semigroup a
monSem _ = %search

export %hint
MonSem : MonoidV a mon => SemigroupV a (monSem mon)
MonSem = MkSemigroupV m_appendAssociative

----------------------------------------------------------------------------------
----          Implementations
----------------------------------------------------------------------------------

export
MonoidV (List a) %search where
  m_appendAssociative = Data.List.appendAssociative _ _ _
  appendRightNeutral  = appendNilRightNeutral _
  appendLeftNeutral   = Refl

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
MonoidV String %search where
  m_appendAssociative = unsafeRefl
  appendRightNeutral  = unsafeRefl
  appendLeftNeutral   = unsafeRefl
