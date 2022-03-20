module Data.Prim.Ring

import Data.Prim.Util

%default total

||| This interface is a witness that for a (primitive)
||| integral type `a` the axioms of a commutative ring hold:
|||
||| 1. `a` is an abelian group under addition:
|||    1. `+` is associative: `k + (m + n) = (k + m) + n` for all `k,m,n : a`.
|||    2. `+` is commutative: `m + n = n + m` for all `m,n : a`.
|||    3. 0 is the additive identity: `n + 0 = n` for all `n : a`.
|||    4. `negate n` is the additive inverse of `n`:
|||       `n + negate n = 0` for all `n : a`.
|||
||| 2. `a` is a commutative monoid under multiplication:
|||    1. `*` is associative: `k * (m * n) = (k * m) * n` for all `k,m,n : a`.
|||    2. `*` is commutative: `m * n = n * m` for all `m,n : a`.
|||    3. 1 is the multiplicative identity: `n * 1 = n` for all `n : a`.
|||
||| 3. Multiplication is distributive with respect to addition:
|||    `k * (m + n) = (k * m) + (k * n)` for all `k,m,n : a`.
|||
||| 4. Subtraction syntax: `m - n = m + negate n` for all `m,n : a`.
public export
interface Neg a => RingLaws a where
  ||| Addition is associative.
  plusAssociative : (0 k,m,n : a) -> k + (m + n) === (k + m) + n

  ||| Addition is commutative.
  plusCommutative : (0 m,n : a) -> m + n === n + m

  ||| 0 is the additive identity.
  plusZeroLeftNeutral : (0 n : a) -> 0 + n === n

  ||| `negate n` is the additive inverse of `n`.
  plusNegateLeftZero : (0 n : a) -> negate n + n === 0

  ||| Multiplication is associative.
  multAssociative : (0 k,m,n : a) -> k * (m * n) === (k * m) * n

  ||| Multiplication is commutative.
  multCommutative : (0 m,n : a) -> m * n === n * m

  ||| 1 is the multiplicative identity.
  multOneLeftNeutral : (0 n : a) -> 1 * n === n

  ||| Multiplication is distributive with respect to addition.
  leftDistributive : (0 k,m,n : a) -> k * (m + n) === (k * m) + (k * n)

  ||| `m - n` is just "syntactic sugar" for `m + negate n`.
  minusIsPlusNegate : (0 m,n : a) -> m - n === m + negate n

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

||| `n + negate n === 0` for all `n : a`.
export
plusNegateRightZero : RingLaws a => (0 n : a) -> n + negate n === 0
plusNegateRightZero n =
  Calc $
    |~ n + negate n
    ~~ negate n + n ...(plusCommutative n (negate n))
    ~~ 0            ...(plusNegateLeftZero n)

||| `n - n === 0` for all `n : a`.
export
minusSelfZero : RingLaws a => (0 n : a) -> n - n === 0
minusSelfZero n =
  Calc $
    |~ n - n
    ~~ n + negate n ...(minusIsPlusNegate n n)
    ~~ 0            ...(plusNegateRightZero n)

||| Law of associativity for subtraction.
export
plusMinusAssociative :  RingLaws a
                     => (0 k,m,n : a)
                     -> k + (m - n) === (k + m) - n
plusMinusAssociative k m n =
  Calc $
    |~ k + (m - n)
    ~~ k + (m + negate n) ...(cong (k+) $ minusIsPlusNegate m n)
    ~~ (k + m) + negate n ...(plusAssociative k m (negate n))
    ~~ (k + m) - n        ...(sym $ minusIsPlusNegate (k + m) n)

||| We can solve equations involving addition.
export
solvePlusRight :  RingLaws a
               => {0 k,m,n : a}
               -> k + m === n
               -> k === n - m
solvePlusRight prf =
  Calc $
    |~ k
    ~~ k + 0        ...(sym $ plusZeroRightNeutral k)
    ~~ k + (m - m)  ...(cong (k +) $ sym $ minusSelfZero m)
    ~~ (k + m) - m  ...(plusMinusAssociative k m m)
    ~~ n - m        ...(cong (\x => x - m) prf)

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
    ~~ (m + n) - n ...(solvePlusRight prf)
    ~~ m + (n - n) ...(sym $ plusMinusAssociative m n n)
    ~~ m + 0       ...(cong (m +) $ minusSelfZero n)
    ~~ m           ...(plusZeroRightNeutral m)

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
solvePlusNegateRight :  RingLaws a
                     => {0 m,n : a}
                     -> m + n === 0
                     -> n === negate m
solvePlusNegateRight prf =
  plusRightInjective (trans prf (sym $ plusNegateRightZero m))

||| From `m + n === 0` follows that `m` is the
||| additive inverse of `n`.
export
solvePlusNegateLeft :  RingLaws a
                    => {0 m,n : a}
                    -> m + n === 0
                    -> m === negate n
solvePlusNegateLeft prf =
  solvePlusNegateRight $ Calc $
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
negateInvolutory : RingLaws a => (0 n : a) -> negate (negate n) === n
negateInvolutory n = sym $ solvePlusNegateLeft (plusNegateRightZero n)

||| From `negate n === 0` follows `n === 0`.
export
negateZero : RingLaws a => {0 n : a} -> negate n === 0 -> n === 0
negateZero prf =
  Calc $
    |~ n
    ~~ n + 0        ...(sym $ plusZeroRightNeutral n)
    ~~ n + negate n ...(cong (n +) $ sym prf)
    ~~ 0            ...(plusNegateRightZero n)

export
negateDistributes :  RingLaws a
                  => {0 m,n : a}
                  -> negate (m + n) === negate m + negate n
negateDistributes =
  let 0 k = negate m + negate n
   in sym $ solvePlusNegateLeft $ Calc $
      |~ (negate m + negate n) + (m + n)
      ~~ (negate m + negate n) + (n + m)  ...(cong ((negate m + negate n) +)
                                             $ plusCommutative m n)
      ~~ ((negate m + negate n) + n) + m  ...(plusAssociative _ _ _)
      ~~ (negate m + (negate n + n)) + m  ...(cong (+m) $ sym
                                             $ plusAssociative _ _ _)
      ~~ (negate m + 0) + m               ...(cong (+m) $ cong (negate m +)
                                             $ plusNegateLeftZero n)
      ~~ negate m + m                     ...(cong (+ m)
                                             $ plusZeroRightNeutral _)
      ~~ 0                                ...(plusNegateLeftZero m)

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
    ~~ n * (0 + 0)       ...(sym $ leftDistributive n 0 0)
    ~~ n * 0             ...(cong (n *) $ plusZeroLeftNeutral 0)

||| Zero is an absorbing element of multiplication.
export
multZeroLeftAbsorbs : RingLaws a => (0 n : a) -> 0 * n === 0
multZeroLeftAbsorbs n =
  Calc $
    |~ 0 * n
    ~~ n * 0 ...(multCommutative 0 n)
    ~~ 0     ...(multZeroRightAbsorbs n)

||| `m * (-n) = - (m * n)`.
export
multNegateRightNegates :  RingLaws a
                       => (0 m,n : a)
                       -> m * negate n === negate (m * n)
multNegateRightNegates m n =
  solvePlusNegateRight $ Calc $
     |~ m * n + m * negate n
     ~~ m * (n + negate n)   ...(sym $ leftDistributive m n (negate n))
     ~~ m * 0                ...(cong (m *) $ plusNegateRightZero n)
     ~~ 0                    ...(multZeroRightAbsorbs m)

||| `(- m) * n = - (m * n)`.
export
multNegateLeftNegates :  RingLaws a
                      => (0 m,n : a)
                      -> negate m * n === negate (m * n)
multNegateLeftNegates m n =
  Calc $
    |~ negate m * n
    ~~ n * negate m   ...(multCommutative (negate m) n)
    ~~ negate (n * m) ...(multNegateRightNegates n m)
    ~~ negate (m * n) ...(cong negate $ multCommutative n m)

||| Multiplication with `(-1)` is negation.
export
multMinusOneRightNegates : RingLaws a => (0 n : a) -> n * negate 1 === negate n
multMinusOneRightNegates n =
  Calc $
    |~ n * negate 1
    ~~ negate (n * 1) ...(multNegateRightNegates n 1)
    ~~ negate n       ...(cong negate $ multOneRightNeutral n)

||| Multiplication with `(-1)` is negation.
export
multMinusOneLeftNegates : RingLaws a => (0 n : a) -> negate 1 * n === negate n
multMinusOneLeftNegates n =
  Calc $
    |~ negate 1 * n
    ~~ negate (1 * n) ...(multNegateLeftNegates 1 n)
    ~~ negate n       ...(cong negate $ multOneLeftNeutral n)

||| Multiplication of two negations removes negations.
export
negateMultNegate : RingLaws a => (m,n : a) -> negate m * negate n === m * n
negateMultNegate m n =
  Calc $
    |~ negate m * negate n
    ~~ negate (m * negate n)   ...(multNegateLeftNegates _ _)
    ~~ negate (negate (m * n)) ...(cong negate $ multNegateRightNegates _ _)
    ~~ m * n                   ...(negateInvolutory _)


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
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Bits16 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Bits32 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Bits64 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Int8 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Int16 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Int32 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Int64 where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Int where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl

export
RingLaws Integer where
  plusAssociative k m n  = unsafeRefl
  plusCommutative m n    = unsafeRefl
  plusZeroLeftNeutral n  = unsafeRefl
  plusNegateLeftZero n   = unsafeRefl
  multAssociative k m n  = unsafeRefl
  multCommutative m n    = unsafeRefl
  multOneLeftNeutral n   = unsafeRefl
  leftDistributive k m n = unsafeRefl
  minusIsPlusNegate m n  = unsafeRefl
