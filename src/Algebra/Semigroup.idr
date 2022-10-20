module Algebra.Semigroup

import Data.List1
import Data.List1.Properties
import Syntax.PreorderReasoning

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a semigroup hold: `(<+>)` is associative.
|||
||| Note: If the type is actually a monoid, use `Data.Algebra.MonoidV` instead.
public export
interface SemigroupV a (0 sem : Semigroup a) | a where
  constructor MkSemigroupV
  0 appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export %inline
SemigroupV (List1 a) %search where
  appendAssociative = Properties.appendAssociative _ _ _
