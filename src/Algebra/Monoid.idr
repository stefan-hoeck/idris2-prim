module Algebra.Monoid


import Data.List
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

--------------------------------------------------------------------------------
--          Monoid
--------------------------------------------------------------------------------

public export
monSem : Monoid a -> Semigroup a
monSem _ = %search

||| This interface is a witness that for a
||| type `a` the axioms of a monoid hold: `(<+>)` is associative
||| with `neutral` being the neutral element.
public export
interface MonoidV a (0 mon : Monoid a) | a where
  constructor MkMonoidV
  0 m_sem : SemigroupV a (monSem mon)

  0 appendLeftNeutral : {x : a} -> Prelude.neutral <+> x === x

  0 appendRightNeutral : {x : a} -> x <+> Prelude.neutral === x

----------------------------------------------------------------------------------
----          Derived Implementations
----------------------------------------------------------------------------------

export %hint
0 MonSem : MonoidV a mon => SemigroupV a (monSem mon)
MonSem = m_sem

----------------------------------------------------------------------------------
----          Implementations
----------------------------------------------------------------------------------

export
MonoidV (List a) %search where
  m_sem = MkSemigroupV (Data.List.appendAssociative _ _ _)
  appendRightNeutral  = appendNilRightNeutral _
  appendLeftNeutral   = Refl

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
MonoidV String %search where
  m_sem = MkSemigroupV unsafeRefl
  appendRightNeutral  = unsafeRefl
  appendLeftNeutral   = unsafeRefl

----------------------------------------------------------------------------------
----          CommutativeSemigroup
----------------------------------------------------------------------------------

||| This interface is a witness that for a
||| type `a` the axioms of a commutative semigroup hold:
||| `(<+>)` is commutative.
public export
interface CommutativeSemigroup a (0 sem : Semigroup a) | a where
  constructor MkCSemigroup
  0 cs_sem : SemigroupV a sem
  0 appendCommutative : {x,y : a} -> x <+> y === y <+> x

----------------------------------------------------------------------------------
----          Derived Implementation
----------------------------------------------------------------------------------

export %hint
0 CSemSem : CommutativeSemigroup a sem => SemigroupV a sem
CSemSem = cs_sem

----------------------------------------------------------------------------------
----          Commutative Monoid
----------------------------------------------------------------------------------

||| This interface is a witness that for a
||| type `a` the axioms of a commutative monoid hold:
||| `(<+>)` is commutative.
public export
interface CommutativeMonoid a (0 mon : Monoid a) | a where
  constructor MkCMonoid
  0 cm_sem : CommutativeSemigroup a (monSem mon)

  0 cm_mon : MonoidV a mon

----------------------------------------------------------------------------------
----          Derived Implementations
----------------------------------------------------------------------------------

export %hint
0 CMonMon : CommutativeMonoid a mon => MonoidV a mon
CMonMon = cm_mon

export %hint
0 CMonCSem : CommutativeMonoid a mon => CommutativeSemigroup a (monSem mon)
CMonCSem = cm_sem

export
0 CMonSem : CommutativeMonoid a mon => SemigroupV a (monSem mon)
CMonSem = CSemSem @{CMonCSem}

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

--------------------------------------------------------------------------------
--          Tests
--------------------------------------------------------------------------------

0 monToSem :
     {mon : _}
  -> MonoidV a mon
  => {x,y,z : a}
  -> x <+> (y <+> z) === (x <+> y) <+> z
monToSem = appendAssociative

0 testListToSem : {x,y,z : List a} -> x <+> (y <+> z) === (x <+> y) <+> z
testListToSem = appendAssociative

0 csemToSem :
     {sem : _}
  -> CommutativeSemigroup a sem
  => {x,y,z : a}
  -> x <+> (y <+> z) === (x <+> y) <+> z
csemToSem = appendAssociative

0 cmonToSem :
     {mon : _}
  -> CommutativeMonoid a mon
  => {x,y,z : a}
  -> x <+> (y <+> z) === (x <+> y) <+> z
cmonToSem = appendAssociative

0 cmonToMon :
     {mon : _}
  -> CommutativeMonoid a mon
  => {x,y,z : a}
  -> x <+> Prelude.neutral === x
cmonToMon = appendRightNeutral

0 cmonToCSem :
     {mon : _}
  -> CommutativeMonoid a mon
  => {x,y,z : a}
  -> x <+> y === y <+> x
cmonToCSem = appendCommutative
