module Data.Prim.Ring

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
interface Neg a => RingLaws a where
  ||| Addition is associative.
  plusAssociative : (0 k,m,n : a) -> k + (m + n) === (k + m) + n

  ||| Addition is commutative.
  plusCommutative : (0 m,n : a) -> m + n === n + m

  ||| 0 is the additive identity.
  plusZeroLeftNeutral : (0 n : a) -> 0 + n === n

  ||| `neg n` is the additive inverse of `n`.
  plusNegLeftZero : (0 n : a) -> neg n + n === 0

  ||| Multiplication is associative.
  multAssociative : (0 k,m,n : a) -> k * (m * n) === (k * m) * n

  ||| Multiplication is commutative.
  multCommutative : (0 m,n : a) -> m * n === n * m

  ||| 1 is the multiplicative identity.
  multOneLeftNeutral : (0 n : a) -> 1 * n === n

  ||| Multiplication is distributive with respect to addition.
  leftDistributive : (0 k,m,n : a) -> k * (m + n) === (k * m) + (k * n)

  ||| `m - n` is just "syntactic sugar" for `m + neg n`.
  minusIsPlusNeg : (0 m,n : a) -> m - n === m + neg n

--------------------------------------------------------------------------------
--          Proofs on Addition
--------------------------------------------------------------------------------

||| `n + 0 === n` for all `n : a`.
export
plusZeroRightNeutral : RingLaws a => (0 n : a) -> n + 0 === n
plusZeroRightNeutral n =
  Calc $
    |~ n + 0
    ~~ 0 + n ...(plusCommutative n 0)
    ~~ n     ...(plusZeroLeftNeutral n)

||| `n + neg n === 0` for all `n : a`.
export
plusNegRightZero : RingLaws a => (0 n : a) -> n + neg n === 0
plusNegRightZero n =
  Calc $
    |~ n + neg n
    ~~ neg n + n ...(plusCommutative n (neg n))
    ~~ 0         ...(plusNegLeftZero n)

||| `n - n === 0` for all `n : a`.
export
minusSelfZero : RingLaws a => (0 n : a) -> n - n === 0
minusSelfZero n =
  Calc $
    |~ n - n
    ~~ n + neg n ...(minusIsPlusNeg n n)
    ~~ 0         ...(plusNegRightZero n)

||| Law of associativity for subtraction.
export
plusMinusAssociative :  RingLaws a
                     => (0 k,m,n : a)
                     -> k + (m - n) === (k + m) - n
plusMinusAssociative k m n =
  Calc $
    |~ k + (m - n)
    ~~ k + (m + neg n) ..>(cong (k+) $ minusIsPlusNeg m n)
    ~~ (k + m) + neg n ..>(plusAssociative k m (neg n))
    ~~ (k + m) - n     ..<(minusIsPlusNeg (k + m) n)

||| We can solve equations involving addition.
export
solvePlusRight :  RingLaws a
               => {0 k,m,n : a}
               -> k + m === n
               -> k === n - m
solvePlusRight prf =
  Calc $
    |~ k
    ~~ k + 0        ..<(plusZeroRightNeutral k)
    ~~ k + (m - m)  ..<(cong (k +) $ minusSelfZero m)
    ~~ (k + m) - m  ..>(plusMinusAssociative k m m)
    ~~ n - m        ..>(cong (\x => x - m) prf)

||| We can solve equations involving addition.
export
solvePlusLeft :  RingLaws a
              => {0 k,m,n : a}
              -> k + m === n
              -> m === n - k
solvePlusLeft prf =
  solvePlusRight $ Calc $
    |~ m + k
    ~~ k + m ...(plusCommutative m k)
    ~~ n     ...(prf)

||| Addition from the left is injective.
export
plusLeftInjective : RingLaws a => {0 k,m,n : a} -> k + n === m + n -> k === m
plusLeftInjective prf =
  Calc $
    |~ k
    ~~ (m + n) - n ..>(solvePlusRight prf)
    ~~ m + (n - n) ..<(plusMinusAssociative m n n)
    ~~ m + 0       ..>(cong (m +) $ minusSelfZero n)
    ~~ m           ..>(plusZeroRightNeutral m)

||| Addition from the right is injective.
export
plusRightInjective : RingLaws a => {0 k,m,n : a} -> n + k === n + m -> k === m
plusRightInjective prf =
  plusLeftInjective $
    Calc $
      |~ k + n
      ~~ n + k  ...(plusCommutative k n)
      ~~ n + m  ...(prf)
      ~~ m + n  ...(plusCommutative n m)

||| From `m + n === 0` follows that `n` is the
||| additive inverse of `m`.
export
solvePlusNegRight :  RingLaws a
                  => {0 m,n : a}
                  -> m + n === 0
                  -> n === neg m
solvePlusNegRight prf =
  plusRightInjective (trans prf (sym $ plusNegRightZero m))

||| From `m + n === 0` follows that `m` is the
||| additive inverse of `n`.
export
solvePlusNegLeft :  RingLaws a
                 => {0 m,n : a}
                 -> m + n === 0
                 -> m === neg n
solvePlusNegLeft prf =
  solvePlusNegRight $ Calc $
    |~ n + m
    ~~ m + n ...(plusCommutative n m)
    ~~ 0     ...(prf)

||| From `m + n === m` follows `n === 0`.
export
solvePlusZeroRight :  RingLaws a => {0 m,n : a} -> m + n === m -> n === 0
solvePlusZeroRight prf =
    Calc $
      |~ n
      ~~ m - m ...(solvePlusLeft prf)
      ~~ 0     ...(minusSelfZero m)

||| From `n + m === m` follows `n === 0`.
export
solvePlusZeroLeft :  RingLaws a => {0 m,n : a} -> n + m === m -> n === 0
solvePlusZeroLeft prf =
    solvePlusZeroRight $ Calc $
      |~ m + n
      ~~ n + m ...(plusCommutative m n)
      ~~ m     ...(prf)

||| Negation is involutory.
export
negInvolutory : RingLaws a => (0 n : a) -> neg (neg n) === n
negInvolutory n = sym $ solvePlusNegLeft (plusNegRightZero n)

||| From `neg n === 0` follows `n === 0`.
export
negZero : RingLaws a => {0 n : a} -> neg n === 0 -> n === 0
negZero prf =
  Calc $
    |~ n
    ~~ n + 0     ..<(plusZeroRightNeutral n)
    ~~ n + neg n ..<(cong (n +) prf)
    ~~ 0         ..>(plusNegRightZero n)

export
negDistributes : RingLaws a => {0 m,n : a} -> neg (m + n) === neg m + neg n
negDistributes =
  sym $ solvePlusNegLeft $ Calc $
  |~ (neg m + neg n) + (m + n)
  ~~ (neg m + neg n) + (n + m)  ...(cong ((neg m + neg n) +)
                                   $ plusCommutative m n)
  ~~ ((neg m + neg n) + n) + m  ...(plusAssociative _ _ _)
  ~~ (neg m + (neg n + n)) + m  ..<(cong (+m) $ plusAssociative _ _ _)
  ~~ (neg m + 0) + m            ...(cong (+m)
                                   $ cong (neg m +) $ plusNegLeftZero n)
  ~~ neg m + m                  ...(cong (+m) $ plusZeroRightNeutral _)
  ~~ 0                          ...(plusNegLeftZero m)

--------------------------------------------------------------------------------
--          Proofs on Multiplication
--------------------------------------------------------------------------------

||| `n * 1 === n` for all `n : a`.
export
multOneRightNeutral : RingLaws a => (0 n : a) -> n * 1 === n
multOneRightNeutral n =
  Calc $
    |~ n * 1
    ~~ 1 * n ...(multCommutative n 1)
    ~~ n     ...(multOneLeftNeutral n)

||| Zero is an absorbing element of multiplication.
export
multZeroRightAbsorbs : RingLaws a => (0 n : a) -> n * 0 === 0
multZeroRightAbsorbs n =
  solvePlusZeroRight $ Calc $
    |~ (n * 0) + (n * 0)
    ~~ n * (0 + 0)       ..<(leftDistributive n 0 0)
    ~~ n * 0             ..>(cong (n *) $ plusZeroLeftNeutral 0)


||| Zero is an absorbing element of multiplication.
export
multZeroLeftAbsorbs : RingLaws a => (0 n : a) -> 0 * n === 0
multZeroLeftAbsorbs n =
  Calc $
    |~ 0 * n
    ~~ n * 0 ...(multCommutative 0 n)
    ~~ 0     ...(multZeroRightAbsorbs n)

||| Zero is an absorbing element of multiplication.
export
multZeroAbsorbs :  RingLaws a
                => (0 m,n : a)
                -> Either (m === 0) (n === 0)
                -> m * n === 0
multZeroAbsorbs m n (Left rfl) =
  Calc $
    |~ m * n
    ~~ 0 * n ...(cong (*n) rfl)
    ~~ 0     ...(multZeroLeftAbsorbs n)

multZeroAbsorbs m n (Right rfl) =
  Calc $
    |~ m * n
    ~~ m * 0 ...(cong (m*) rfl)
    ~~ 0     ...(multZeroRightAbsorbs m)

||| `m * (-n) = - (m * n)`.
export
multNegRight : RingLaws a => (0 m,n : a) -> m * neg n === neg (m * n)
multNegRight m n =
  solvePlusNegRight $ Calc $
     |~ m * n + m * neg n
     ~~ m * (n + neg n)   ..<(leftDistributive m n (neg n))
     ~~ m * 0             ..>(cong (m *) $ plusNegRightZero n)
     ~~ 0                 ..>(multZeroRightAbsorbs m)

||| `- (m * (-n)) = m * n`.
export
negMultNegRight : RingLaws a => (0 m,n : a) -> neg (m * neg n) === m * n
negMultNegRight m n =
  Calc $
    |~ neg (m * neg n)
    ~~ neg (neg (m * n)) ...(cong neg $ multNegRight _ _)
    ~~ m * n             ...(negInvolutory _)

||| `(- m) * n = - (m * n)`.
export
multNegLeft : RingLaws a => (0 m,n : a) -> neg m * n === neg (m * n)
multNegLeft m n =
  Calc $
    |~ neg m * n
    ~~ n * neg m   ...(multCommutative (neg m) n)
    ~~ neg (n * m) ...(multNegRight n m)
    ~~ neg (m * n) ...(cong neg $ multCommutative n m)

||| `- ((-m) * n) = m * n`.
export
negMultNegLeft : RingLaws a => (0 m,n : a) -> neg (neg m * n) === m * n
negMultNegLeft m n =
  Calc $
    |~ neg (neg m * n)
    ~~ neg (neg (m * n)) ...(cong neg $ multNegLeft _ _)
    ~~ m * n             ...(negInvolutory _)

||| Multiplication with `(-1)` is negation.
export
multMinusOneRight : RingLaws a => (0 n : a) -> n * neg 1 === neg n
multMinusOneRight n =
  Calc $
    |~ n * neg 1
    ~~ neg (n * 1) ...(multNegRight n 1)
    ~~ neg n       ...(cong neg $ multOneRightNeutral n)

||| Multiplication with `(-1)` is negation.
export
multMinusOneLeft : RingLaws a => (0 n : a) -> neg 1 * n === neg n
multMinusOneLeft n =
  Calc $
    |~ neg 1 * n
    ~~ neg (1 * n) ...(multNegLeft 1 n)
    ~~ neg n       ...(cong neg $ multOneLeftNeutral n)

||| Multiplication of two negations removes negations.
export
negMultNeg : RingLaws a => (m,n : a) -> neg m * neg n === m * n
negMultNeg m n =
  Calc $
    |~ neg m * neg n
    ~~ neg (m * neg n)   ...(multNegLeft _ _)
    ~~ neg (neg (m * n)) ...(cong neg $ multNegRight _ _)
    ~~ m * n             ...(negInvolutory _)

||| Multiplication is distributive with respect to addition.
export
rightDistributive :  RingLaws a
                  => (0 k,m,n : a)
                  -> (m + n) * k === (k * m) + (k * n)
rightDistributive k m n =
  Calc $
    |~ (m + n) * k
    ~~ k * (m + n)       ...(multCommutative _ _)
    ~~ (k * m) + (k * n) ...(leftDistributive _ _ _)

export
multPlusSelf : RingLaws a => (m,n : a) -> m * n + m === m * (n + 1)
multPlusSelf m n =
  Calc $
    |~ m * n + m
    ~~ m * n + m * 1 ..<(cong (m*n +) $ multOneRightNeutral m)
    ~~ m * (n + 1)   ..<(leftDistributive m n 1)

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

export
RingLaws Bits8 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Bits16 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Bits32 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Bits64 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Int8 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Int16 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Int32 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Int64 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Int where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl

export
RingLaws Integer where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegLeftZero n      = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNeg m n     = unsafeRefl
