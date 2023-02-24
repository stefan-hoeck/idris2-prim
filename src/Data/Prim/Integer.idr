module Data.Prim.Integer

import public Control.WellFounded
import public Data.Prim.Ord
import public Algebra.Solver.Ring
import Syntax.PreorderReasoning

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

export %inline
Total Integer (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

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
0 multPosPosGT0 : (m,n : Integer) -> 0 < m -> 0 < n -> 0 < m * n
multPosPosGT0 _ _ p1 p2 = strictLT p1 $ strictLT p2 $ mkLT unsafeRefl

||| There is no integer between 0 and 1.
export
0 oneAfterZero : (n : Integer) -> 0 < n -> 1 <= n
oneAfterZero n gt0 = case comp 1 n of
  LT x _ _ => Left x
  EQ _ x _ => Right x
  GT _ _ x => strictLT gt0
            $ strictLT x
            $ assert_total
            $ idris_crash "IMPOSSIBLE: Integer between 0 and 1"

||| For positive `d`, `mod n d` is a non-negative number
||| strictly smaller than `d`.
export
0 modLT : (n,d : Integer) -> 0 < d -> (0 <= mod n d, mod n d < d)
modLT n d x with (mod n d)
  _ | 0 = (Right Refl, x)
  _ | _ = strictLT x (Left $ mkLT unsafeRefl, mkLT unsafeRefl)

export
0 modNegEQ : (n,d : Integer) -> d < 0 -> mod n d === mod n (negate d)
modNegEQ n d x = strictLT x unsafeRefl

export
0 lawDivMod : (n,d : Integer) -> d /= 0 -> d * div n d + mod n d === n
lawDivMod n d (Left x)  = strictLT x unsafeRefl
lawDivMod n d (Right x) = strictLT x unsafeRefl

----------------------------
-- Division

||| Safe division.
export %inline
sdiv : (n,d : Integer) -> (0 prf : d /= 0) => Integer
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Integer) -> (0 prf : d /= 0) => Integer
smod n d = n `mod` d

--------------------------------------------------------------------------------
--          Well-Foundedness
--------------------------------------------------------------------------------

public export
0 BoundedLT : (lowerBound : Integer) -> Integer -> Integer -> Type
BoundedLT lowerBound x y = (lowerBound <= x, x < y)

public export
0 BoundedGT : (upperBound : Integer) -> Integer -> Integer -> Type
BoundedGT upperBound x y = (upperBound >= x, x > y)

||| Every value of type `Integer` with a fixed lower bound
||| is accessible with relation to `(<)`.
export
accessLT : (m : Integer) -> Accessible (BoundedLT lb) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| Every value of type `Integer` with a fixed upper bound
||| is accessible with relation to `(>)`.
export
accessGT : (m : Integer) -> Accessible (BoundedGT ub) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)
