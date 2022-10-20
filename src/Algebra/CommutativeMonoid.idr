module Algebra.CommutativeMonoid

import public Algebra.Monoid
import public Algebra.Semigroup
import public Algebra.CommutativeSemigroup
import Syntax.PreorderReasoning

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a commutative monoid hold:
||| `(<+>)` is commutative.
public export
interface CommutativeMonoid a (0 mon : Monoid a) | a where
  constructor MkCMonoidV
  0 cm_appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z

  0 cm_appendLeftNeutral : {x : a} -> Prelude.neutral <+> x === x

  0 cm_appendCommutative : {x,y : a} -> x <+> y === y <+> x

0 cm_appendRightNeutral :
    {mon : _}
  -> CommutativeMonoid a mon
  => {x : a}
  -> x <+> Prelude.neutral === x
cm_appendRightNeutral = Calc $
  |~ x <+> neutral
  ~~ neutral <+> x ... cm_appendCommutative
  ~~ x             ... cm_appendLeftNeutral

----------------------------------------------------------------------------------
----          Derived Implementations
----------------------------------------------------------------------------------

export %hint
CMonMon : CommutativeMonoid a mon => MonoidV a mon
CMonMon = MkMonoidV
  cm_appendAssociative
  cm_appendLeftNeutral
  cm_appendRightNeutral

export %hint
CMonCSem : CommutativeMonoid a mon => CommutativeSemigroup a (monSem mon)
CMonCSem = MkCSemigroup
  cm_appendAssociative
  cm_appendCommutative

export
CMonSem : CommutativeMonoid a mon => SemigroupV a (monSem mon)
CMonSem = CSemSem @{CMonCSem}
