module Algebra.Semiring

import Data.Nat
import public Algebra.Monoid
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Solvable Numeric Types
--------------------------------------------------------------------------------

public export
interface SolvableNum a (0 num : Num a) | a where
  constructor MkSolvableNum

  ||| Test if the given values equals zero. This is needed during
  ||| normalization of expressions
  num_isZero : (v : a) -> Maybe (v === 0)

||| When normalizing arithmetic expressions, we must
||| make sure that factors which evaluate to zero must
||| be removed from the sum of products.
|||
||| For instance, the following example only works,
||| if the term `0 * x * y` gets removed before comparing
||| the normalized sums:
|||
||| ```idris example
||| 0 binom3 : {x,y : Bits8} -> (x + y) * (x - y) === x * x - y * y
||| binom3 = solve [x,y] ((x .+. y) * (x .-. y)) (x .*. x - y .*. y)
||| ```
|||
||| Because we cannot directly use a (primitive) pattern match
||| without having a concrete type, we need this interface.
||| (We *could* use `DecEq`, but this is not publicly exported
||| for the primitives; probably for good reasons since it is
||| implemented using `believe_me`).
public export
interface SolvableNeg a (0 neg : Neg a) | a where
  constructor MkSolvableNeg
  ||| Test if the given values equals zero. This is needed during
  ||| normalization of expressions
  neg_isZero : (v : a) -> Maybe (v === 0)

--------------------------------------------------------------------------------
--          Solvable Implementations
--------------------------------------------------------------------------------

public export %inline
negNum : Neg a -> Num a
negNum _ = %search

public export %hint
NegNum : SolvableNeg a neg => SolvableNum a (negNum neg)
NegNum = MkSolvableNum neg_isZero

public export
SolvableNum Nat %search where
  num_isZero Z = Just Refl
  num_isZero _ = Nothing

public export
SolvableNeg Bits8 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Bits16 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Bits32 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Bits64 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Int8 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Int16 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Int32 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Int64 %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Int %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

public export
SolvableNeg Integer %search where
  neg_isZero 0 = Just Refl
  neg_isZero _ = Nothing

--------------------------------------------------------------------------------
--          Semiring
--------------------------------------------------------------------------------

||| This interface is a witness that for a
||| numeric type `a` the axioms of a commutative semiring hold:
|||
||| 1. `a` is a commutative monoid under addition:
|||    1. `+` is associative: `k + (m + n) = (k + m) + n` for all `k,m,n : a`.
|||    2. `+` is commutative: `m + n = n + m` for all `m,n : a`.
|||    3. 0 is the additive identity: `n + 0 = n` for all `n : a`.
|||
||| 2. `a` is a commutative monoid under multiplication:
|||    1. `*` is associative: `k * (m * n) = (k * m) * n` for all `k,m,n : a`.
|||    2. `*` is commutative: `m * n = n * m` for all `m,n : a`.
|||    3. 1 is the multiplicative identity: `n * 1 = n` for all `n : a`.
|||
||| 3. Multiplication is distributive with respect to addition:
|||    `k * (m + n) = (k * m) + (k * n)` for all `k,m,n : a`.
|||
public export
interface Semiring a (0 num : Num a) | a where
  constructor MkSemiring

  ||| Addition is associative.
  0 plusAssociative : {k,m,n : a} -> k + (m + n) === (k + m) + n

  ||| Addition is commutative.
  0 plusCommutative : {m,n : a} -> m + n === n + m

  ||| 0 is the additive identity.
  0 plusZeroLeftNeutral : {n : a} -> 0 + n === n

  ||| Multiplication is associative.
  0 multAssociative : {k,m,n : a} -> k * (m * n) === (k * m) * n

  ||| Multiplication is commutative.
  0 multCommutative : {m,n : a} -> m * n === n * m

  ||| 1 is the multiplicative identity.
  0 multOneLeftNeutral : {n : a} -> 1 * n === n

  ||| Multiplication is distributive with respect to addition.
  0 leftDistributive : {k,m,n : a} -> k * (m + n) === (k * m) + (k * n)

  ||| Zero is an absorbing element of multiplication.
  0 multZeroLeftAbsorbs : {n : a} -> 0 * n === 0

--------------------------------------------------------------------------------
--          Proofs on Addition
--------------------------------------------------------------------------------

||| `n + 0 === n` for all `n : a`.
export
0 plusZeroRightNeutral :
     {num : _}
  -> Semiring a num
  => {n : a}
  -> n + 0 === n
plusZeroRightNeutral =
  Calc $
    |~ n + 0
    ~~ 0 + n ... plusCommutative
    ~~ n     ... plusZeroLeftNeutral

--------------------------------------------------------------------------------
--          Proofs on Multiplication
--------------------------------------------------------------------------------

||| `n * 1 === n` for all `n : a`.
export
0 multOneRightNeutral :
     {num : _}
  -> Semiring a num
  => {n : a}
  -> n * 1 === n
multOneRightNeutral =
  Calc $
    |~ n * 1
    ~~ 1 * n ... multCommutative
    ~~ n     ... multOneLeftNeutral

||| Zero is an absorbing element of multiplication.
export
0 multZeroRightAbsorbs :
     {num : _}
  -> Semiring a num
  => {n : a}
  -> n * 0 === 0
multZeroRightAbsorbs =
  Calc $
    |~ n * 0
    ~~ 0 * n ... multCommutative
    ~~ 0     ... multZeroLeftAbsorbs

||| Zero is an absorbing element of multiplication.
export
multZeroAbsorbs :
     {num : _}
  -> Semiring a num
  => (m,n : a)
  -> Either (m === 0) (n === 0)
  -> m * n === 0
multZeroAbsorbs m n (Left rfl) =
  Calc $
    |~ m * n
    ~~ 0 * n ... cong (*n) rfl
    ~~ 0     ... multZeroLeftAbsorbs

multZeroAbsorbs m n (Right rfl) =
  Calc $
    |~ m * n
    ~~ m * 0 ... cong (m*) rfl
    ~~ 0     ... multZeroRightAbsorbs

||| Multiplication is distributive with respect to addition.
export
0 rightDistributive :
     {num : _}
  -> Semiring a num
  => {k,m,n : a}
  -> (m + n) * k === m * k + n * k
rightDistributive =
  Calc $
    |~ (m + n) * k
    ~~ k * (m + n)       ... multCommutative
    ~~ (k * m) + (k * n) ... leftDistributive
    ~~ m * k + k * n     ... cong (+ k * n) multCommutative
    ~~ m * k + n * k     ... cong (m * k +) multCommutative

export
0 multPlusSelf :
     {num : _}
  -> Semiring a num
  => {m,n : a}
  -> m * n + m === m * (n + 1)
multPlusSelf =
  Calc $
    |~ m * n + m
    ~~ m * n + m * 1 ..< cong (m*n +) multOneRightNeutral
    ~~ m * (n + 1)   ..< leftDistributive

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

public export
Semiring Nat %search where
  plusAssociative = Nat.plusAssociative _ _ _
  plusCommutative = Nat.plusCommutative _ _
  plusZeroLeftNeutral = Nat.plusZeroLeftNeutral _
  multAssociative = Nat.multAssociative _ _ _
  multCommutative = Nat.multCommutative _ _
  multOneLeftNeutral = Nat.multOneLeftNeutral _
  leftDistributive = multDistributesOverPlusRight _ _ _
  multZeroLeftAbsorbs = Refl

public export %inline
[PlusSem] Num a => Semigroup a where
  (<+>) = (+)

public export %inline
[PlusMon] Num a => Monoid a using PlusSem where
  neutral = 0

public export %inline
[MultSem] Num a => Semigroup a where
  (<+>) = (*)

public export %inline
[MultMon] Num a => Monoid a using MultSem where
  neutral = 1

0 sr_semiPlus : {num : _} -> Semiring a num => SemigroupV a PlusSem
sr_semiPlus = MkSemigroupV plusAssociative

export
0 SRPlusCMon : {num : _} -> Semiring a num => CommutativeMonoid a PlusMon
SRPlusCMon = MkCMonoid
  (MkCSemigroup sr_semiPlus plusCommutative)
  (MkMonoidV  sr_semiPlus plusZeroLeftNeutral plusZeroRightNeutral)

export
0 SRPlusMon : {num : _} -> Semiring a num => MonoidV a PlusMon
SRPlusMon = CMonMon @{SRPlusCMon}

export
0 SRPlusCSem : {num : _} -> Semiring a num => CommutativeSemigroup a PlusSem
SRPlusCSem = CMonCSem @{SRPlusCMon}

export
0 SRPlusSem : {num : _} -> Semiring a num => SemigroupV a PlusSem
SRPlusSem = CMonSem @{SRPlusCMon}

0 sr_semiMult : {num : _} -> Semiring a num => SemigroupV a MultSem
sr_semiMult = MkSemigroupV multAssociative

export
0 SRMultCMon : {num : _} -> Semiring a num => CommutativeMonoid a MultMon
SRMultCMon = MkCMonoid
  (MkCSemigroup sr_semiMult multCommutative)
  (MkMonoidV  sr_semiMult multOneLeftNeutral multOneRightNeutral)

export
0 SRMultMon : {num : _} -> Semiring a num => MonoidV a MultMon
SRMultMon = CMonMon @{SRMultCMon}

export
0 SRMultCSem : {num : _} -> Semiring a num => CommutativeSemigroup a MultSem
SRMultCSem = CMonCSem @{SRMultCMon}

export
0 SRMultSem : {num : _} -> Semiring a num => SemigroupV a MultSem
SRMultSem = CMonSem @{SRMultCMon}
