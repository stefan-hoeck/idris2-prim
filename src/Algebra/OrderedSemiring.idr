module Algebra.OrderedSemiring

import public Algebra.Semiring
import public Data.Prim.Ord
import Data.Nat
import public Syntax.Total

%default total

||| An ordered semiring is a semiring with a total ordering `lt` and two
||| additional laws:
|||
||| 1.  `x < y` => `x + z < y + z` for all `x`, `y`, `z`
|||
||| 2. `0 < n`, `k < m` => `n * k < n * m` for all `k`, `m`, `n`
public export
interface OrderedSemiring a (0 num : Num a) (0 lt : a -> a -> Type) | a where
  constructor MkOrderedSemiring

  0 ossr : Semiring a num

  ||| Axiom I: `<` is transitive.
  0 osr_transLT : {k,m,n : a} -> lt k m -> lt m n -> lt k n

  0 plusLeftLT : {k,m,n : a} -> lt k m -> lt (n + k) (n + m)

  0 multGT : {k,m,n : a} -> lt 0 n -> lt k m -> lt (n * k) (n * m)

  ||| Axiom II: Trichotomy of `<`, `===`, and `>`.
  osr_trichotomy : (m,n : a) -> Trichotomy lt m n

public export %inline %hint
SROrdered : OrderedSemiring a num lt => Total a lt
SROrdered = MkTotal (osr_transLT {a}) osr_trichotomy

public export %inline %hint
0 OSSR : OrderedSemiring a num lt => Semiring a num
OSSR = ossr

--------------------------------------------------------------------------------
--          Discrete Semiring
--------------------------------------------------------------------------------

||| A discrete semiring is a total semiring, with no values between
||| 0 and 1:
|||
||| 1. `0 < n => 1 <= n` for all `n`
|||
||| The most important descrete (commutative) semiring in Idris are the
||| natural numbers `Nat`.
public export
interface DiscreteSemiring a (0 num : Num a) (0 lt : a -> a -> Type) | a where
  constructor MkDiscreteSemiring

  0 dsr : Semiring a num

  ||| Axiom I: `<` is transitive.
  0 ds_transLT : {k,m,n : a} -> lt k m -> lt m n -> lt k n

  0 ds_plusLeftLT : {k,m,n : a} -> lt k m -> lt (n + k) (n + m)

  0 ds_multGT : {k,m,n : a} -> lt 0 n -> lt k m -> lt (n * k) (n * m)

  ||| In a discrete semiring, there is no value between 0 and 1.
  0 discrete : {n : a} -> lt 0 n -> LTE lt 1 n

  ||| Axiom II: Trichotomy of `<`, `===`, and `>`.
  ds_trichotomy : (m,n : a) -> Trichotomy lt m n

public export %inline %hint
DSOrdered : DiscreteSemiring a num lt => OrderedSemiring a num lt
DSOrdered = MkOrderedSemiring
  dsr
  (ds_transLT {a})
  (ds_plusLeftLT {a})
  (ds_multGT {a})
  ds_trichotomy

public export %hint
0 DSSR : DiscreteSemiring a num lt => Semiring a num
DSSR = OSSR @{DSOrdered}

--------------------------------------------------------------------------------
--          Addition Lemmata
--------------------------------------------------------------------------------

||| Adding a value on the left does not affect an inequality.
export
0 plusLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt k m
  -> Rel b lt (n + k) (n + m)
plusLeft (EQ p) = EQ $ cong (n +) p
plusLeft (LT p) = LT $ plusLeftLT {a} p

||| Adding a value on the right does not affect an inequality.
export
0 plusRight :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt k m
  -> Rel b lt (k + n) (m + n)
plusRight rel = CalcAny $
   |~ k + n
   <~ n + k .=. plusCommutative @{OSSR}
   <! n + m ... plusLeft {lt} rel
   <~ m + n .=. plusCommutative @{OSSR}

||| The result of adding a non-negative value is greater than
||| or equal to the original.
export
0 plusNonNegRight :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt 0 m
  -> Rel b lt n (n + m)
plusNonNegRight rel = CalcAny $
  |~ n
  <~ n + 0 .~. plusZeroRightNeutral @{OSSR}
  <! n + m ... plusLeft {a} rel

||| The result of adding a non-negative value is greater than
||| or equal to the original.
export
0 plusNonNegLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt 0 m
  -> Rel b lt n (m + n)
plusNonNegLeft rel = CalcAny $
  |~ n
  <~ 0 + n .~. plusZeroLeftNeutral @{OSSR}
  <! m + n ... plusRight {a} rel

||| The result of adding a non-positive value is less than
||| or equal to the original.
export
0 plusNonPosRight :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt m 0
  -> Rel b lt (n + m) n
plusNonPosRight rel = CalcAny $
  |~ n + m
  <! n + 0 ... plusLeft {a} rel
  <~ n     .=. plusZeroRightNeutral @{OSSR}

||| The result of adding a non-positive value is less than
||| or equal to the original.
export
0 plusNonPosLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt m 0
  -> Rel b lt (m + n) n
plusNonPosLeft rel = CalcAny $
  |~ m + n
  <! 0 + n ... plusRight {a} rel
  <~ n     .=. plusZeroLeftNeutral @{OSSR}

||| From `n + k < n + m` follows `k < m`. Likewise for `<=`.
export
0 solvePlusLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt (n + k) (n + m)
  -> Rel b lt k m
solvePlusLeft rel = case trichotomy @{SROrdered} k m of
  LT x _ _ => LT x
  EQ _ p _ => case b of
    True  => void $ LT_not_EQ (toLT rel) (cong (n+) p)
    False => EQ p
  GT _ _ x => void $ LTE_not_GT (toLTE rel) (plusLeftLT {a} x)

||| From `k + n < m + n` follows `k < m`. Likewise for `<=`.
export
0 solvePlusRight :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt (k + n) (m + n)
  -> Rel b lt k m
solvePlusRight rel = solvePlusLeft {a} $ CalcAny $
  |~ n + k
  <~ k + n .=. plusCommutative @{OSSR}
  <! m + n ... rel
  <~ n + m .=. plusCommutative @{OSSR}

||| We can solve (in)equalities, with one side an addition
||| and the other equalling the added value.
export
0 solvePlusRightSelf :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt n (k + n)
  -> Rel b lt 0 k
solvePlusRightSelf rel =
  solvePlusRight $ transR (EQ $ plusZeroLeftNeutral @{OSSR}) rel

||| We can solve (in)equalities, with one side an addition
||| and the other equalling the added value.
export
0 solvePlusLeftSelf :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt n (n + k)
  -> Rel b lt 0 k
solvePlusLeftSelf rel =
  solvePlusLeft $ transR (EQ $ plusZeroRightNeutral @{OSSR}) rel

--------------------------------------------------------------------------------
--          Multiplication Lemmata
--------------------------------------------------------------------------------

export
0 multPos :
     {num : _}
  -> OrderedSemiring a num lt
  => lt 0 m
  -> Rel b lt 0 n
  -> Rel b lt 0 (m * n)
multPos p (LT q) = CalcAny $
  |~ 0
  <~ m * 0 .~. multZeroRightAbsorbs @{OSSR}
  <! m * n ... LT (multGT {a} p q)

multPos p (EQ q) = EQ $ Calc $
  |~ 0
  ~~ m * 0 ..< multZeroRightAbsorbs @{OSSR}
  ~~ m * n ... cong (m*) q

export
0 multPosLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => lt 0 n
  -> Rel b lt k m
  -> Rel b lt (n * k) (n * m)
multPosLeft p (LT q) = LT $ multGT {a} p q
multPosLeft _ (EQ q) = EQ $ cong (n *) q

export
0 multPosRight :
     {num : _}
  -> OrderedSemiring a num lt
  => lt 0 n
  -> Rel b lt k m
  -> Rel b lt (k * n) (m * n)
multPosRight x rel = CalcAny $
  |~ k * n
  <~ n * k .=. multCommutative @{OSSR}
  <! n * m ... multPosLeft x rel
  <~ m * n .=. multCommutative @{OSSR}

export
0 multNonNegLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt 0 n
  -> lt k m
  -> Rel b lt (n * k) (n * m)
multNonNegLeft (LT p) y = multPosLeft p (LT y)
multNonNegLeft (EQ p) y = EQ $ Calc $
  |~ n * k
  ~~ 0 * k ..< cong (*k) p
  ~~ 0     ... multZeroLeftAbsorbs @{OSSR}
  ~~ 0 * m ..< multZeroLeftAbsorbs @{OSSR}
  ~~ n * m ... cong (*m) p

export
0 multNonNegRight :
     {num : _}
  -> OrderedSemiring a num lt
  => Rel b lt 0 n
  -> lt k m
  -> Rel b lt (k * n) (m * n)
multNonNegRight x rel = CalcAny $
  |~ k * n
  <~ n * k .=. multCommutative @{OSSR}
  <! n * m ... multNonNegLeft x rel
  <~ m * n .=. multCommutative @{OSSR}

export
0 solveMultPosLeft :
     {num : _}
  -> OrderedSemiring a num lt
  => lt 0 n
  -> Rel b lt (n * k) (n * m)
  -> Rel b lt k m
solveMultPosLeft q rel = case trichotomy @{SROrdered} k m of
  LT x _ _ => LT x
  EQ _ p _ => case b of
    True  => void $ LT_not_EQ (toLT rel) (cong (n*) p)
    False => EQ p
  GT _ _ x => void $ LTE_not_GT (toLTE rel) (toLT $ multPosLeft {a} q $ LT x)

export
0 solveMultPosRight :
     {num : _}
  -> OrderedSemiring a num lt
  => lt 0 n
  -> Rel b lt (k * n) (m * n)
  -> Rel b lt k m
solveMultPosRight x rel =
  let rel' := CalcAny $
        |~ n * k
        <~ k * n .=. multCommutative @{OSSR}
        <! m * n ... rel
        <~ n * m .=. multCommutative @{OSSR}
   in solveMultPosLeft x rel'

--------------------------------------------------------------------------------
--          Nat Implementation
--------------------------------------------------------------------------------

0 natSemi : Semiring Nat %search
natSemi = MkSemiring
   (Nat.plusAssociative _ _ _)
   (Nat.plusCommutative _ _)
   (Nat.plusZeroLeftNeutral _)
   (Nat.multAssociative _ _ _)
   (Nat.multCommutative _ _)
   (Nat.multOneLeftNeutral _)
   (multDistributesOverPlusRight _ _ _)
   Refl

0 ltOpReflLT : (m,n : Nat) -> (m < n) === True -> LT m n
ltOpReflLT 0     (S k) prf = LTESucc LTEZero
ltOpReflLT (S k) (S j) prf = LTESucc (ltOpReflLT k j prf)
ltOpReflLT (S k) 0     prf impossible
ltOpReflLT 0 0         prf impossible

0 ltOpReflEQ : (m,n : Nat) -> (m < n) === False -> (n < m) === False -> m === n
ltOpReflEQ 0     0     p q = Refl
ltOpReflEQ (S k) (S j) p q = cong S $ ltOpReflEQ k j p q
ltOpReflEQ (S k) 0     p q impossible
ltOpReflEQ 0     (S k) p q impossible

0 LTImpliesNotGT : (m,n : Nat) -> LT m n -> Not (LT n m)
LTImpliesNotGT (S k) (S j) (LTESucc x) (LTESucc y) = LTImpliesNotGT k j x y
LTImpliesNotGT 0 0     x y impossible
LTImpliesNotGT 0 (S k) x y impossible
LTImpliesNotGT (S k) 0 x y impossible

0 EQImpliesNotLT : (m,n : Nat) -> m === n -> Not (LT m n)
EQImpliesNotLT 0    0      prf x impossible
EQImpliesNotLT 0    (S k)  prf x           = absurd prf
EQImpliesNotLT (S k) 0     prf x           = absurd prf
EQImpliesNotLT (S k) (S j) prf (LTESucc x) =
  EQImpliesNotLT k j (injective prf) x

0 LTImpliesNotEQ : (m,n : Nat) -> LT m n -> Not (m === n)
LTImpliesNotEQ m n = flip $ EQImpliesNotLT m n

export
comp : (m,n : Nat) -> Trichotomy LT m n
comp m n with (m < n) proof eq
  comp m n | True  =
    let 0 p := ltOpReflLT m n eq
     in LT p (LTImpliesNotEQ m n p) (LTImpliesNotGT m n p)
  comp m n | False with (n < m) proof eq2
    comp m n | False | True  =
      let 0 p := ltOpReflLT n m eq2
       in GT (LTImpliesNotGT n m p) (\e => LTImpliesNotEQ n m p $ sym e) p
    comp m n | False | False =
      let 0 p := ltOpReflEQ m n eq eq2
       in EQ (EQImpliesNotLT m n p) p (EQImpliesNotLT n m $ sym p)

0 plusImpl : (n : Nat) -> LT k m -> LT (n + k) (n + m)
plusImpl 0     x = x
plusImpl (S j) x = LTESucc $ plusImpl j x

0 lte1 : (n : Nat) -> LTE 1 (S n)
lte1 0     = %search
lte1 (S k) = lteSuccRight $ lte1 k

0 ltePlusRight : (k,m,n : Nat) -> LTE k m -> LTE k (n + m)
ltePlusRight k m 0 x = x
ltePlusRight k m (S j) x = lteSuccRight $ ltePlusRight k m j x

0 ltePlus : (k,l,m,n : Nat) -> LTE k l -> LTE m n -> LTE (k + m) (l + n)
ltePlus 0 l m n LTEZero y = ltePlusRight m n l y
ltePlus (S left) (S right) m n (LTESucc x) y =
  LTESucc $ ltePlus left right m n x y

0 multImpl1 : (k,m,n : Nat) -> LTE k m -> LTE (n * k) (n * m)
multImpl1 k m 0     x = LTEZero
multImpl1 k m (S j) x = ltePlus _ _ _ _ x $ multImpl1 k m j x

0 multImpl : (k,m,n : Nat) -> LT 0 n -> LT k m -> LT (n * k) (n * m)
multImpl k m 0 x y = absurd x
multImpl k m (S j) x y =
  let prf := multImpl1 k m j (lteSuccLeft y)
   in ltePlus (S k) m (j * k) (j * m) y prf

0 discreteImpl : (n : Nat) -> LT 0 n -> LTE LT 1 n
discreteImpl 0         x = absurd x
discreteImpl (S 0)     x = Right Refl
discreteImpl (S (S k)) x = Left $ LTESucc $ lte1 k

public export %inline
DiscreteSemiring Nat %search LT where
  ds_trichotomy = comp
  discrete p = discreteImpl _ p
  ds_multGT p1 p2 = multImpl _ _ _ p1 p2
  ds_plusLeftLT = plusImpl n
  ds_transLT x y = transitive x (lteSuccLeft y)
  dsr = natSemi
