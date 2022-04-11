module Algebra.Semiring

import Data.Nat
import Syntax.PreorderReasoning

%default total

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
interface Num a => Semiring a where
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
0 plusZeroRightNeutral : Semiring a => {n : a} -> n + 0 === n
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
0 multOneRightNeutral : Semiring a => {n : a} -> n * 1 === n
multOneRightNeutral =
  Calc $
    |~ n * 1
    ~~ 1 * n ... multCommutative
    ~~ n     ... multOneLeftNeutral

||| Zero is an absorbing element of multiplication.
export
0 multZeroRightAbsorbs : Semiring a => {n : a} -> n * 0 === 0
multZeroRightAbsorbs =
  Calc $
    |~ n * 0
    ~~ 0 * n ... multCommutative
    ~~ 0     ... multZeroLeftAbsorbs

||| Zero is an absorbing element of multiplication.
export
multZeroAbsorbs :  Semiring a
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
0 rightDistributive :  Semiring a
                  => {k,m,n : a}
                  -> (m + n) * k === m * k + n * k
rightDistributive =
  Calc $
    |~ (m + n) * k
    ~~ k * (m + n)       ... multCommutative
    ~~ (k * m) + (k * n) ... leftDistributive
    ~~ m * k + k * n     ... cong (+ k * n) multCommutative
    ~~ m * k + n * k     ... cong (m * k +) multCommutative

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

export
Semiring Nat where
  plusAssociative = Nat.plusAssociative _ _ _
  plusCommutative = Nat.plusCommutative _ _
  plusZeroLeftNeutral = Nat.plusZeroLeftNeutral _
  multAssociative = Nat.multAssociative _ _ _
  multCommutative = Nat.multCommutative _ _
  multOneLeftNeutral = Nat.multOneLeftNeutral _
  leftDistributive = multDistributesOverPlusRight _ _ _
  multZeroLeftAbsorbs = Refl
