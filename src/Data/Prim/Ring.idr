module Data.Prim.Ring

import Data.Prim.Util

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
--          Proofs on (+)
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

export
plusLeftInjective : RingLaws a => {0 k,m,n : a} -> k + n === m + n -> k === m
plusLeftInjective prf =
  Calc $
    |~ k
    ~~ (m + n) - n ...(solvePlusRight prf)
    ~~ m + (n - n) ...(sym $ plusMinusAssociative m n n)
    ~~ m + 0       ...(cong (m +) $ minusSelfZero n)
    ~~ m           ...(plusZeroRightNeutral m)

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
