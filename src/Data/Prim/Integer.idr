module Data.Prim.Integer

import public Control.WellFounded
import public Data.DPair
import public Data.Prim.Ord
import public Data.Prim.Ring

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

--------------------------------------------------------------------------------
--          (<)
--------------------------------------------------------------------------------

||| Witness that `m < n === True`.
export
data (<) : (m,n : Integer) -> Type where
  LT : {0 m,n : Integer} -> (0 prf : (m < n) === True) -> m < n

||| Contructor for `(<)`.
|||
||| This can only be used in an erased context.
export %hint
0 mkLT : (0 prf : (m < n) === True) -> m < n
mkLT = LT

||| Extractor for `(<)`.
|||
||| This can only be used in an erased context.
export
0 runLT : m < n -> (m < n) === True
runLT (LT prf) = prf

||| We don't trust values of type `(<)` too much,
||| so we use this when creating magical results.
export
strictLT : (0 p : m < n) -> Lazy c -> c
strictLT (LT prf) x = x

--------------------------------------------------------------------------------
--          Aliases
--------------------------------------------------------------------------------

||| Flipped version of `(<)`.
public export
0 (>) : (m,n : Integer) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Integer) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Integer) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Integer) -> Type
m /= n = Either (m < n) (m > n)

--------------------------------------------------------------------------------
--          Order
--------------------------------------------------------------------------------

0 ltNotEQ : m < n -> Not (m === n)
ltNotEQ x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and EQ")

0 ltNotGT : m < n -> Not (n < m)
ltNotGT x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and GT")

0 eqNotLT : m === n -> Not (m < n)
eqNotLT = flip ltNotEQ

export
comp : (m,n : Integer) -> Trichotomy (<) m n
comp m n = case prim__lt_Integer m n of
  0 => case prim__eq_Integer m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Strict Integer (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

replace' : (0 p : a -> Type) -> (0 _ : x = y) -> p x -> p y
replace' p prf px = replace {p} prf px

---------
-- Axioms

||| This axiom, which only holds for unbounded integers, relates
||| addition and the ordering of integers:
|||
||| From `k < m` follows `n + k < n + m` for all integers `k`, `m`, and `n`.
export
0 plusGT : (k,m,n : Integer) -> k < m -> n + k < n + m
plusGT k m n x = strictLT x $ mkLT unsafeRefl

||| This axiom, which only holds for unbounded integers, relates
||| multiplication and the ordering of integers:
|||
||| From `0 < m` and `0 < n` follows `0 < m * n` for all integers `m` and `n`.
export
0 multGT : (m,n : Integer) -> 0 < m -> 0 < n -> 0 < m * n
multGT _ _ p1 p2 = strictLT p1 $ strictLT p2 $ mkLT unsafeRefl


-----------
-- Addition

||| This axiom, which only holds for unbounded integers, relates
||| addition and the ordering of integers:
|||
||| From `k < m` follows `k + n < m + n` for all integers `k`, `m`, and `n`.
export
0 plusGT' : (k,m,n : Integer) -> k < m -> k + n < m + n
plusGT' k m n lt =
  replace' (< m + n) (plusCommutative n k) $
  replace' (n + k <) (plusCommutative n m) $
  plusGT k m n lt

||| The result of adding a positive number to `m` is strictly greater
||| than `m`.
export
0 plusPositiveGT : (m,n : Integer) -> 0 < n -> m < m + n
plusPositiveGT m n lt =
  replace' (< m + n) (plusZeroRightNeutral m) (plusGT 0 n m lt)


||| The result of adding a negative number to `m` is strictly less
||| than `m`.
export
0 plusNegativeLT : (m,n : Integer) -> n < 0 -> m > m + n
plusNegativeLT m n lt =
  replace' (> m + n) (plusZeroRightNeutral m) (plusGT n 0 m lt)

||| From `m < m + n` follows `n > 0`.
export
0 solvePlusGT : (m,n : Integer) -> m < m + n -> 0 < n
solvePlusGT m n lt = case comp 0 n of
  LT x _    _ => x
  EQ _ Refl _ => void (LT_not_EQ lt (sym $ plusZeroRightNeutral m))
  GT _ _    x => void (LT_not_GT lt $ plusNegativeLT m n x)

||| From `m > m + n` follows `n < 0`.
export
0 solvePlusLT : (m,n : Integer) -> m > m + n -> n < 0
solvePlusLT m n lt = case comp 0 n of
  LT x _    _ => void (LT_not_GT lt $ plusPositiveGT m n x)
  EQ _ Refl _ => void (GT_not_EQ lt (sym $ plusZeroRightNeutral m))
  GT _ _    x => x

||| From `k < m` and `l < n` follows `k + l < m + n`.
export
0 plusPositiveTwice : (k,l,m,n : Integer) -> k < m -> l < n -> k + l < m + n
plusPositiveTwice k l m n kltm lltn =
  trans (plusGT l n k lltn) (plusGT' k m n kltm)

||| Adding two positive numbers yields a positive number.
export
0 addPositiveGT0 : (m,n : Integer) -> 0 < m -> 0 < n -> 0 < m + n
addPositiveGT0 = plusPositiveTwice 0 0

||| From `0 < n` follows `negate n < 0`.
export
0 negatePositiveNegative : (n : Integer) -> 0 < n -> 0 > negate n
negatePositiveNegative n gt0 = case comp 0 (negate n) of
  LT x _ _ =>
    void (GT_not_EQ (addPositiveGT0 _ _ gt0 x) (plusNegateRightZero n))
  EQ _ x _ =>
    void (GT_not_EQ gt0 $ negateZero (sym x))
  GT _ _ x => x


----------------------------
-- Safe and refined division

||| Safe division.
export %inline
sdiv : (n,d : Integer) -> (0 prf : d /= 0) => Integer
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Integer) -> (0 prf : d /= 0) => Integer
smod n d = n `mod` d

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| The square root of a non-negative integer `n` is the
||| unique integer `v` with `v >= 0`, `v * v <= n`,
||| and `(v + 1) * (v + 1) > n`.
public export
record Sqrt (n : Integer) where
  constructor MkSqrt
  value : Integer
  0 nonNegative : 0 <= value
  0 ltn         : value * value <= n
  0 gtn         : (value + 1) * (value + 1) > n

||| Computes the integer square root of a non-negative integer
||| using a binary search.
export
sqrt : (n : Integer) -> (0 prf : 0 <= n) => Sqrt n
sqrt n = case comp 0 n of
  GT _ _ x => void $ LT_not_GTE x prf
  EQ _ x _ => replace' Sqrt x (MkSqrt 0 %search %search %search)
  LT x _ _ => case comp 1 n of
    EQ _ y _ => ?foo_1
    GT _ _ y => ?foo_2
    LT y _ _ => ?foo_0


