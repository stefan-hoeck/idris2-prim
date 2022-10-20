module Algebra.Ring

import public Algebra.Semiring
import Syntax.PreorderReasoning

%default total

||| This interface is a witness that for a (primitive)
||| integral type `a` the axioms of a commutative ring hold:
|||
||| 1. `a` is an abelian group under addition:
|||    1. `+` is associative: `k + (m + n) = (k + m) + n` for all `k,m,n : a`.
|||    2. `+` is commutative: `m + n = n + m` for all `m,n : a`.
|||    3. 0 is the additive identity: `n + 0 = n` for all `n : a`.
|||    4. `neg n` is the additive inverse of `n`:
|||       `n + neg n = 0` for all `n : a`.
|||
||| 2. `a` is a commutative monoid under multiplication:
|||    1. `*` is associative: `k * (m * n) = (k * m) * n` for all `k,m,n : a`.
|||    2. `*` is commutative: `m * n = n * m` for all `m,n : a`.
|||    3. 1 is the multiplicative identity: `n * 1 = n` for all `n : a`.
|||
||| 3. Multiplication is distributive with respect to addition:
|||    `k * (m + n) = (k * m) + (k * n)` for all `k,m,n : a`.
|||
||| 4. Subtraction syntax: `m - n = m + neg n` for all `m,n : a`.
public export
interface Ring a (0 neg : Neg a) | a where
  constructor MkRing

  ||| Addition is associative.
  0 r_plusAssociative : {k,m,n : a} -> k + (m + n) === (k + m) + n

  ||| Addition is commutative.
  0 r_plusCommutative : {m,n : a} -> m + n === n + m

  ||| 0 is the additive identity.
  0 r_plusZeroLeftNeutral : {n : a} -> 0 + n === n

  ||| `neg n` is the additive inverse of `n`.
  0 plusNegLeftZero : {n : a} -> negate n + n === 0

  ||| Multiplication is associative.
  0 r_multAssociative : {k,m,n : a} -> k * (m * n) === (k * m) * n

  ||| Multiplication is commutative.
  0 r_multCommutative : {m,n : a} -> m * n === n * m

  ||| 1 is the multiplicative identity.
  0 r_multOneLeftNeutral : {n : a} -> 1 * n === n

  ||| Multiplication is distributive with respect to addition.
  0 r_leftDistributive : {k,m,n : a} -> k * (m + n) === (k * m) + (k * n)

  ||| `m - n` is just "syntactic sugar" for `m + neg n`.
  0 minusIsPlusNeg : {m,n : a} -> m - n === m + negate n

--------------------------------------------------------------------------------
--          Named Implementations
--------------------------------------------------------------------------------

||| Zero is an absorbing element of multiplication.
export
0 r_multZeroLeftAbsorbs : {neg : _} -> Ring a neg => {n : a} -> 0 * n === 0

export %hint
RSR : Ring a neg => Semiring a (negNum neg)
RSR = MkSemiring
  r_plusAssociative
  r_plusCommutative
  r_plusZeroLeftNeutral
  r_multAssociative
  r_multCommutative
  r_multOneLeftNeutral
  r_leftDistributive
  r_multZeroLeftAbsorbs

export
RPlusCMon : {neg : _} -> Ring a neg => CommutativeMonoid a PlusMon
RPlusCMon = SRPlusCMon @{RSR}

export
RPlusMon : {neg : _} -> Ring a neg => MonoidV a PlusMon
RPlusMon = SRPlusMon @{RSR}

export
RPlusCSem : {neg : _} -> Ring a neg => CommutativeSemigroup a PlusSem
RPlusCSem = SRPlusCSem @{RSR}

export
RPlusSem : {neg : _} -> Ring a neg => SemigroupV a PlusSem
RPlusSem = SRPlusSem @{RSR}

export
RMultCMon : {neg : _} -> Ring a neg => CommutativeMonoid a MultMon
RMultCMon = SRMultCMon @{RSR}

export
RMultMon : {neg : _} -> Ring a neg => MonoidV a MultMon
RMultMon = SRMultMon @{RSR}

export
RMultCSem : {neg : _} -> Ring a neg => CommutativeSemigroup a MultSem
RMultCSem = SRMultCSem @{RSR}

export
RMultSem : {neg : _} -> Ring a neg => SemigroupV a MultSem
RMultSem = SRMultSem @{RSR}

--------------------------------------------------------------------------------
--          Proofs on Addition
--------------------------------------------------------------------------------

||| `n + neg n === 0` for all `n : a`.
export
0 plusNegRightZero :
     {neg : _}
   -> Ring a neg
   => {n : a}
   -> n + negate n === 0
plusNegRightZero =
  Calc $
    |~ n + negate n
    ~~ negate n + n ... plusCommutative
    ~~ 0            ... plusNegLeftZero

||| `n - n === 0` for all `n : a`.
export
0 minusSelfZero : {neg : _} -> Ring a neg => {n : a} -> n - n === 0
minusSelfZero =
  Calc $
    |~ n - n
    ~~ n + negate n ... minusIsPlusNeg
    ~~ 0            ... plusNegRightZero

||| Law of associativity for subtraction.
export
0 plusMinusAssociative :
     {neg : _}
  -> Ring a neg
  => {k,m,n : a}
  -> k + (m - n) === (k + m) - n
plusMinusAssociative =
  Calc $
    |~ k + (m - n)
    ~~ k + (m + negate n) ..> cong (k+) minusIsPlusNeg
    ~~ (k + m) + negate n ..> plusAssociative
    ~~ (k + m) - n        ..< minusIsPlusNeg

||| We can solve equations involving addition.
export
0 solvePlusRight :
     {neg : _}
  -> Ring a neg
  => {k,m,n : a}
  -> k + m === n
  -> k === n - m
solvePlusRight prf =
  Calc $
    |~ k
    ~~ k + 0        ..< plusZeroRightNeutral
    ~~ k + (m - m)  ..< cong (k +) minusSelfZero
    ~~ (k + m) - m  ..> plusMinusAssociative
    ~~ n - m        ..> cong (\x => x - m) prf

||| We can solve equations involving addition.
export
0 solvePlusLeft :
     {neg : _}
  -> Ring a neg
  => {k,m,n : a}
  -> k + m === n
  -> m === n - k
solvePlusLeft prf =
  solvePlusRight $ Calc $
    |~ m + k
    ~~ k + m ... plusCommutative
    ~~ n     ... prf

||| Addition from the left is injective.
export
0 plusLeftInjective :
     {neg : _}
  -> Ring a neg
  => {k,m,n : a}
  -> k + n === m + n
  -> k === m
plusLeftInjective prf =
  Calc $
    |~ k
    ~~ (m + n) - n ..> solvePlusRight prf
    ~~ m + (n - n) ..< plusMinusAssociative
    ~~ m + 0       ..> cong (m +) minusSelfZero
    ~~ m           ..> plusZeroRightNeutral

||| Addition from the right is injective.
export
0 plusRightInjective :
     {neg : _}
  -> Ring a neg
  => {k,m,n : a}
  -> n + k === n + m
  -> k === m
plusRightInjective prf =
  plusLeftInjective $
    Calc $
      |~ k + n
      ~~ n + k  ... plusCommutative
      ~~ n + m  ... prf
      ~~ m + n  ... plusCommutative

||| From `m + n === 0` follows that `n` is the
||| additive inverse of `m`.
export
0 solvePlusNegRight :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> m + n === 0
  -> n === negate m
solvePlusNegRight prf =
  plusRightInjective (trans prf (sym plusNegRightZero))

||| From `m + n === 0` follows that `m` is the
||| additive inverse of `n`.
export
0 solvePlusNegLeft :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> m + n === 0
  -> m === negate n
solvePlusNegLeft prf =
  solvePlusNegRight $ Calc $
    |~ n + m
    ~~ m + n ... plusCommutative
    ~~ 0     ... prf

||| From `m + n === m` follows `n === 0`.
export
0 solvePlusZeroRight :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> m + n === m
  -> n === 0
solvePlusZeroRight prf =
    Calc $
      |~ n
      ~~ m - m ... solvePlusLeft prf
      ~~ 0     ... minusSelfZero

||| From `n + m === m` follows `n === 0`.
export
0 solvePlusZeroLeft :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> n + m === m
  -> n === 0
solvePlusZeroLeft prf =
    solvePlusZeroRight $ Calc $
      |~ m + n
      ~~ n + m ... plusCommutative
      ~~ m     ... prf

||| Negation is involutory.
export
0 negInvolutory : {neg : _} -> Ring a neg => {n : a} -> negate (negate n) === n
negInvolutory = sym $ solvePlusNegLeft plusNegRightZero

||| From `neg n === 0` follows `n === 0`.
export
0 solveNegZero :
     {neg : _}
  -> Ring a neg
  => {n : a}
  -> negate n === 0
  -> n === 0
solveNegZero prf =
  Calc $
    |~ n
    ~~ n + 0        ..< plusZeroRightNeutral
    ~~ n + negate n ..< cong (n +) prf
    ~~ 0            ..> plusNegRightZero

||| `negate 0 === 0`
export
0 negZero : {neg : _} -> Ring a neg => negate (the a 0) === 0
negZero = solveNegZero negInvolutory

export
0 negDistributes :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> negate (m + n) === negate m + negate n
negDistributes =
  sym $ solvePlusNegLeft $ Calc $
  |~ (negate m + negate n) + (m + n)
  ~~ (negate m + negate n) + (n + m)
     ... cong ((negate m + negate n) +) plusCommutative
  ~~ ((negate m + negate n) + n) + m
     ... r_plusAssociative
  ~~ (negate m + (negate n + n)) + m
     ..< cong (+m) plusAssociative
  ~~ (negate m + 0) + m
     ... cong (\x => negate m + x + m) plusNegLeftZero
  ~~ negate m + m
     ... cong (+m) plusZeroRightNeutral
  ~~ 0
     ... plusNegLeftZero

--------------------------------------------------------------------------------
--          Proofs on Multiplication
--------------------------------------------------------------------------------

r_multZeroLeftAbsorbs =
  Calc $
    |~ 0 * n
    ~~ n * 0 ... multCommutative
    ~~ 0     ... multZeroRightAbsorbs

||| Zero is an absorbing element of multiplication.
export
0 multZeroAbsorbs :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> Either (m === 0) (n === 0)
  -> m * n === 0
multZeroAbsorbs (Left rfl) =
  Calc $
    |~ m * n
    ~~ 0 * n ... cong (*n) rfl
    ~~ 0     ... multZeroLeftAbsorbs

multZeroAbsorbs (Right rfl) =
  Calc $
    |~ m * n
    ~~ m * 0 ... cong (m*) rfl
    ~~ 0     ... multZeroRightAbsorbs

||| `m * (-n) = - (m * n)`.
export
0 multNegRight :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> m * negate n === negate (m * n)
multNegRight =
  solvePlusNegRight $ Calc $
     |~ m * n + m * negate n
     ~~ m * (n + negate n) ..< leftDistributive
     ~~ m * 0              ..> cong (m *) plusNegRightZero
     ~~ 0                  ..> multZeroRightAbsorbs

||| `- (m * (-n)) = m * n`.
export
0 negMultNegRight :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> negate (m * negate n) === m * n
negMultNegRight =
  Calc $
    |~ negate (m * negate n)
    ~~ negate (negate (m * n)) ... cong negate multNegRight
    ~~ m * n                   ... negInvolutory

||| `(- m) * n = - (m * n)`.
export
0 multNegLeft :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> negate m * n === negate (m * n)
multNegLeft =
  Calc $
    |~ negate m * n
    ~~ n * negate m   ... multCommutative
    ~~ negate (n * m) ... multNegRight
    ~~ negate (m * n) ... cong negate multCommutative

||| `- ((-m) * n) = m * n`.
export
0 negMultNegLeft :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> negate (negate m * n) === m * n
negMultNegLeft =
  Calc $
    |~ negate (negate m * n)
    ~~ negate (negate (m * n)) ... cong negate multNegLeft
    ~~ m * n                   ... negInvolutory

||| Multiplication with `(-1)` is negation.
export
0 multMinusOneRight :
     {neg : _}
  -> Ring a neg
  => {n : a}
  -> n * negate 1 === negate n
multMinusOneRight =
  Calc $
    |~ n * negate 1
    ~~ negate (n * 1) ... multNegRight
    ~~ negate n       ... cong negate multOneRightNeutral

||| Multiplication with `(-1)` is negation.
export
0 multMinusOneLeft :
     {neg : _}
  -> Ring a neg
  => {n : a}
  -> negate 1 * n === negate n
multMinusOneLeft =
  Calc $
    |~ negate 1 * n
    ~~ negate (1 * n) ... multNegLeft
    ~~ negate n       ... cong negate multOneLeftNeutral

||| Multiplication of two negations removes negations.
export
0 negMultNeg :
     {neg : _}
  -> Ring a neg
  => {m,n : a}
  -> negate m * negate n === m * n
negMultNeg =
  Calc $
    |~ negate m * negate n
    ~~ negate (m * negate n)   ... multNegLeft
    ~~ negate (negate (m * n)) ... cong negate multNegRight
    ~~ m * n                   ... negInvolutory

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
Ring Bits8 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Bits16 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Bits32 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Bits64 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Int8 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Int16 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Int32 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Int64 %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Int %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl

export
Ring Integer %search where
  r_plusAssociative     = unsafeRefl
  r_plusCommutative     = unsafeRefl
  r_plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero       = unsafeRefl
  r_multAssociative     = unsafeRefl
  r_multCommutative     = unsafeRefl
  r_multOneLeftNeutral  = unsafeRefl
  r_leftDistributive    = unsafeRefl
  minusIsPlusNeg        = unsafeRefl
