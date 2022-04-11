module Algebra.Ring

import Syntax.PreorderReasoning

%default total

public export %inline %tcinline
neg : Neg a => a -> a
neg = negate

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
interface Neg a => Ring a where
  ||| Addition is associative.
  0 plusAssociative : {k,m,n : a} -> k + (m + n) === (k + m) + n

  ||| Addition is commutative.
  0 plusCommutative : {m,n : a} -> m + n === n + m

  ||| 0 is the additive identity.
  0 plusZeroLeftNeutral : {n : a} -> 0 + n === n

  ||| `neg n` is the additive inverse of `n`.
  0 plusNegLeftZero : {n : a} -> neg n + n === 0

  ||| Multiplication is associative.
  0 multAssociative : {k,m,n : a} -> k * (m * n) === (k * m) * n

  ||| Multiplication is commutative.
  0 multCommutative : {m,n : a} -> m * n === n * m

  ||| 1 is the multiplicative identity.
  0 multOneLeftNeutral : {n : a} -> 1 * n === n

  ||| Multiplication is distributive with respect to addition.
  0 leftDistributive : {k,m,n : a} -> k * (m + n) === (k * m) + (k * n)

  ||| `m - n` is just "syntactic sugar" for `m + neg n`.
  0 minusIsPlusNeg : {m,n : a} -> m - n === m + neg n

--------------------------------------------------------------------------------
--          Proofs on Addition
--------------------------------------------------------------------------------

||| `n + 0 === n` for all `n : a`.
export
0 plusZeroRightNeutral : Ring a => {n : a} -> n + 0 === n
plusZeroRightNeutral =
  Calc $
    |~ n + 0
    ~~ 0 + n ... plusCommutative
    ~~ n     ... plusZeroLeftNeutral

||| `n + neg n === 0` for all `n : a`.
export
0 plusNegRightZero : Ring a => {n : a} -> n + neg n === 0
plusNegRightZero =
  Calc $
    |~ n + neg n
    ~~ neg n + n ... plusCommutative
    ~~ 0         ... plusNegLeftZero

||| `n - n === 0` for all `n : a`.
export
0 minusSelfZero : Ring a => {n : a} -> n - n === 0
minusSelfZero =
  Calc $
    |~ n - n
    ~~ n + neg n ... minusIsPlusNeg
    ~~ 0         ... plusNegRightZero

||| Law of associativity for subtraction.
export
0 plusMinusAssociative :  Ring a
                       => {k,m,n : a}
                       -> k + (m - n) === (k + m) - n
plusMinusAssociative =
  Calc $
    |~ k + (m - n)
    ~~ k + (m + neg n) ..> cong (k+) minusIsPlusNeg
    ~~ (k + m) + neg n ..> plusAssociative
    ~~ (k + m) - n     ..< minusIsPlusNeg

||| We can solve equations involving addition.
export
0 solvePlusRight :  Ring a
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
0 solvePlusLeft :  Ring a
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
0 plusLeftInjective : Ring a => {k,m,n : a} -> k + n === m + n -> k === m
plusLeftInjective prf =
  Calc $
    |~ k
    ~~ (m + n) - n ..> solvePlusRight prf
    ~~ m + (n - n) ..< plusMinusAssociative
    ~~ m + 0       ..> cong (m +) minusSelfZero
    ~~ m           ..> plusZeroRightNeutral

||| Addition from the right is injective.
export
0 plusRightInjective : Ring a => {k,m,n : a} -> n + k === n + m -> k === m
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
0 solvePlusNegRight :  Ring a
                    => {m,n : a}
                    -> m + n === 0
                    -> n === neg m
solvePlusNegRight prf =
  plusRightInjective (trans prf (sym plusNegRightZero))

||| From `m + n === 0` follows that `m` is the
||| additive inverse of `n`.
export
0 solvePlusNegLeft :  Ring a
                   => {m,n : a}
                   -> m + n === 0
                   -> m === neg n
solvePlusNegLeft prf =
  solvePlusNegRight $ Calc $
    |~ n + m
    ~~ m + n ... plusCommutative
    ~~ 0     ... prf

||| From `m + n === m` follows `n === 0`.
export
0 solvePlusZeroRight :  Ring a => {m,n : a} -> m + n === m -> n === 0
solvePlusZeroRight prf =
    Calc $
      |~ n
      ~~ m - m ... solvePlusLeft prf
      ~~ 0     ... minusSelfZero

||| From `n + m === m` follows `n === 0`.
export
0 solvePlusZeroLeft :  Ring a => {m,n : a} -> n + m === m -> n === 0
solvePlusZeroLeft prf =
    solvePlusZeroRight $ Calc $
      |~ m + n
      ~~ n + m ... plusCommutative
      ~~ m     ... prf

||| Negation is involutory.
export
0 negInvolutory : Ring a => {n : a} -> neg (neg n) === n
negInvolutory = sym $ solvePlusNegLeft plusNegRightZero

||| From `neg n === 0` follows `n === 0`.
export
0 solveNegZero : Ring a => {n : a} -> neg n === 0 -> n === 0
solveNegZero prf =
  Calc $
    |~ n
    ~~ n + 0     ..< plusZeroRightNeutral
    ~~ n + neg n ..< cong (n +) prf
    ~~ 0         ..> plusNegRightZero

||| `neg 0 === 0`
export
0 negZero : Ring a => neg {a} 0 === 0
negZero = solveNegZero negInvolutory

export
0 negDistributes : Ring a => {m,n : a} -> neg (m + n) === neg m + neg n
negDistributes =
  sym $ solvePlusNegLeft $ Calc $
  |~ (neg m + neg n) + (m + n)
  ~~ (neg m + neg n) + (n + m) ... cong ((neg m + neg n) +) plusCommutative
  ~~ ((neg m + neg n) + n) + m ... plusAssociative
  ~~ (neg m + (neg n + n)) + m ..< cong (+m) plusAssociative
  ~~ (neg m + 0) + m           ... cong (\x => neg m + x + m) plusNegLeftZero
  ~~ neg m + m                 ... cong (+m) plusZeroRightNeutral
  ~~ 0                         ... plusNegLeftZero

--------------------------------------------------------------------------------
--          Proofs on Multiplication
--------------------------------------------------------------------------------

||| `n * 1 === n` for all `n : a`.
export
0 multOneRightNeutral : Ring a => {n : a} -> n * 1 === n
multOneRightNeutral =
  Calc $
    |~ n * 1
    ~~ 1 * n ... multCommutative
    ~~ n     ... multOneLeftNeutral

||| Zero is an absorbing element of multiplication.
export
0 multZeroRightAbsorbs : Ring a => {n : a} -> n * 0 === 0
multZeroRightAbsorbs =
  solvePlusZeroRight $ Calc $
    |~ (n * 0) + (n * 0)
    ~~ n * (0 + 0)       ..< leftDistributive
    ~~ n * 0             ..> cong (n *) plusZeroLeftNeutral


||| Zero is an absorbing element of multiplication.
export
0 multZeroLeftAbsorbs : Ring a => {n : a} -> 0 * n === 0
multZeroLeftAbsorbs =
  Calc $
    |~ 0 * n
    ~~ n * 0 ... multCommutative
    ~~ 0     ... multZeroRightAbsorbs

||| Zero is an absorbing element of multiplication.
export
0 multZeroAbsorbs :  Ring a
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
0 multNegRight : Ring a => {m,n : a} -> m * neg n === neg (m * n)
multNegRight =
  solvePlusNegRight $ Calc $
     |~ m * n + m * neg n
     ~~ m * (n + neg n)   ..< leftDistributive
     ~~ m * 0             ..> cong (m *) plusNegRightZero
     ~~ 0                 ..> multZeroRightAbsorbs

||| `- (m * (-n)) = m * n`.
export
0 negMultNegRight : Ring a => {m,n : a} -> neg (m * neg n) === m * n
negMultNegRight =
  Calc $
    |~ neg (m * neg n)
    ~~ neg (neg (m * n)) ... cong neg multNegRight
    ~~ m * n             ... negInvolutory

||| `(- m) * n = - (m * n)`.
export
0 multNegLeft : Ring a => {m,n : a} -> neg m * n === neg (m * n)
multNegLeft =
  Calc $
    |~ neg m * n
    ~~ n * neg m   ... multCommutative
    ~~ neg (n * m) ... multNegRight
    ~~ neg (m * n) ... cong neg multCommutative

||| `- ((-m) * n) = m * n`.
export
0 negMultNegLeft : Ring a => {m,n : a} -> neg (neg m * n) === m * n
negMultNegLeft =
  Calc $
    |~ neg (neg m * n)
    ~~ neg (neg (m * n)) ... cong neg multNegLeft
    ~~ m * n             ... negInvolutory

||| Multiplication with `(-1)` is negation.
export
0 multMinusOneRight : Ring a => {n : a} -> n * neg 1 === neg n
multMinusOneRight =
  Calc $
    |~ n * neg 1
    ~~ neg (n * 1) ... multNegRight
    ~~ neg n       ... cong neg multOneRightNeutral

||| Multiplication with `(-1)` is negation.
export
0 multMinusOneLeft : Ring a => {n : a} -> neg 1 * n === neg n
multMinusOneLeft =
  Calc $
    |~ neg 1 * n
    ~~ neg (1 * n) ... multNegLeft
    ~~ neg n       ... cong neg multOneLeftNeutral

||| Multiplication of two negations removes negations.
export
0 negMultNeg : Ring a => {m,n : a} -> neg m * neg n === m * n
negMultNeg =
  Calc $
    |~ neg m * neg n
    ~~ neg (m * neg n)   ... multNegLeft
    ~~ neg (neg (m * n)) ... cong neg multNegRight
    ~~ m * n             ... negInvolutory

||| Multiplication is distributive with respect to addition.
export
0 rightDistributive :  Ring a
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
0 multPlusSelf : Ring a => {m,n : a} -> m * n + m === m * (n + 1)
multPlusSelf =
  Calc $
    |~ m * n + m
    ~~ m * n + m * 1 ..< cong (m*n +) multOneRightNeutral
    ~~ m * (n + 1)   ..< leftDistributive

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
Ring Bits8 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Bits16 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Bits32 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Bits64 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Int8 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Int16 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Int32 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Int64 where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Int where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl

export
Ring Integer where
  plusAssociative     = unsafeRefl
  plusCommutative     = unsafeRefl
  plusZeroLeftNeutral = unsafeRefl
  plusNegLeftZero     = unsafeRefl
  multAssociative     = unsafeRefl
  multCommutative     = unsafeRefl
  multOneLeftNeutral  = unsafeRefl
  leftDistributive    = unsafeRefl
  minusIsPlusNeg      = unsafeRefl
