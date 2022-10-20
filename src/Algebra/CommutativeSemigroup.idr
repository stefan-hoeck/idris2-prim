module Algebra.CommutativeSemigroup

import Algebra.Semigroup as S
import Syntax.PreorderReasoning

%default total

||| This interface is a witness that for a
||| type `a` the axioms of a commutative semigroup hold:
||| `(<+>)` is commutative.
public export
interface CommutativeSemigroup a (0 sem : Semigroup a) | a where
  constructor MkCSemigroup
  0 cs_appendAssociative : {x,y,z : a} -> x <+> (y <+> z) === (x <+> y) <+> z
  0 appendCommutative : {x,y : a} -> x <+> y === y <+> x

----------------------------------------------------------------------------------
----          Derived Implementation
----------------------------------------------------------------------------------

export %hint
CSemSem : CommutativeSemigroup a sem => SemigroupV a sem
CSemSem = MkSemigroupV cs_appendAssociative

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| A utility proof that is used several times internally
export
0 lemma1324 :
     {sem : _}
  -> CommutativeSemigroup a sem
  => {k,l,m,n : a}
  -> (k <+> l) <+> (m <+> n) === (k <+> m) <+> (l <+> n)
lemma1324 = Calc $
  |~ (k <+> l) <+> (m <+> n)
  ~~ ((k <+> l) <+> m) <+> n ... appendAssociative
  ~~ (k <+> (l <+> m)) <+> n ..< cong (<+>n) appendAssociative
  ~~ (k <+> (m <+> l)) <+> n ... cong (\x => (k <+> x) <+> n) appendCommutative
  ~~ ((k <+> m) <+> l) <+> n ... cong (<+>n) appendAssociative
  ~~ (k <+> m) <+> (l <+> n) ..< appendAssociative

||| A utility proof that is used several times internally
export
0 lemma213 :
     {sem : _}
  -> CommutativeSemigroup a sem
  => {k,m,n : a}
  -> k <+> (m <+> n) === m <+> (k <+> n)
lemma213 = Calc $
  |~ k <+> (m <+> n)
  ~~ (k <+> m) <+> n   ... appendAssociative
  ~~ (m <+> k) <+> n   ... cong (<+> n) appendCommutative
  ~~ m <+> (k <+> n)   ..< appendAssociative
