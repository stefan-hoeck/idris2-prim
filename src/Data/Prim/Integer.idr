module Data.Prim.Integer

import public Control.WellFounded
import public Data.DPair
import public Data.Prim.Ord
import public Data.Prim.Ring
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
0 modNegLT : (n,d : Integer) -> d < 0 -> mod n d === mod n (neg d)
modNegLT n d x = strictLT x unsafeRefl

export
0 lawDivMod : (n,d : Integer) -> d /= 0 -> d * div n d + mod n d === n
lawDivMod n d (Left x)  = strictLT x unsafeRefl
lawDivMod n d (Right x) = strictLT x unsafeRefl

-----------
-- Addition

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

||| The result of adding a non-negative number to `m` is not less
||| than `m`.
export
0 plusNonNegativeGTE : (m,n : Integer) -> 0 <= n -> m <= m + n
plusNonNegativeGTE m n (Left x) = Left $ plusPositiveGT m n x
plusNonNegativeGTE m n (Right x) =
  Right $ Calc $
    |~ m
    ~~ m + 0 ...(sym $ plusZeroRightNeutral m)
    ~~ m + n ...(cong (m +) x)

||| The result of adding a negative number to `m` is strictly less
||| than `m`.
export
0 plusNegativeLT : (m,n : Integer) -> n < 0 -> m > m + n
plusNegativeLT m n lt =
  replace' (> m + n) (plusZeroRightNeutral m) (plusGT n 0 m lt)

||| The result of adding a non-positive number to `m` is not greater
||| than `m`.
export
0 plusNonPositiveLTE : (m,n : Integer) -> n <= 0 -> m >= m + n
plusNonPositiveLTE m n (Left x) = Left $ plusNegativeLT m n x
plusNonPositiveLTE m n (Right x) =
  Right $ Calc $
    |~ m + n
    ~~ m + 0 ...(cong (m+) x)
    ~~ m     ...(plusZeroRightNeutral m)

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

||| From `k < m` and `l <= n` follows `k + l < m + n`.
export
0 plusGT2 : (k,l,m,n : Integer) -> k < m -> l <= n -> k + l < m + n
plusGT2 k l m n x (Left y) = trans (plusGT l n k y) (plusGT' k m n x)
plusGT2 k l m n x (Right y) =
  replace' (\q => k + q < m + n) (sym y) (plusGT' _ _ _ x)

||| Adding a positive number to a non-negative number
||| yields a positive number.
export
0 plusPositiveGT0 : (m,n : Integer) -> 0 < m -> 0 <= n -> 0 < m + n
plusPositiveGT0 = plusGT2 0 0

||| Adding a negative number to a non-positive number yields a negative number.
export
0 plusNegativeLT0 : (m,n : Integer) -> m < 0 -> n <= 0 -> m + n < 0
plusNegativeLT0 m n = plusGT2 m n 0 0

||| From `0 < n` follows `neg n < 0`.
export
0 negPositiveNegative : (n : Integer) -> 0 < n -> 0 > neg n
negPositiveNegative n gt0 = case comp 0 (neg n) of
  LT x _ _ =>
    void (GT_not_EQ (plusPositiveGT0 _ _ gt0 $ Left x) (plusNegRightZero n))
  EQ _ x _ => void (GT_not_EQ gt0 $ negZero (sym x))
  GT _ _ x => x

||| From `n < 0` follows `0 < neg n`.
export
0 negNegativePositive : (n : Integer) -> n < 0 -> neg n > 0
negNegativePositive n lt0 = case comp 0 (neg n) of
  LT x _ _ => x
  EQ _ x _ => void (LT_not_EQ lt0 $ negZero (sym x))
  GT _ _ x =>
    void (LT_not_EQ (plusNegativeLT0 _ _ lt0 %search) (plusNegRightZero n))

||| From `m < n` follows `0 < n - m`.
export
0 minusSmallerPositive : (m,n : Integer) -> m < n -> n - m > 0
minusSmallerPositive m n lt = solvePlusGT m (n - m) (replace' (m <) lemma lt)
  where lemma : n === m + (n - m)
        lemma = Calc $
          |~ n
          ~~ n + 0       ...(sym $ plusZeroRightNeutral n)
          ~~ n + (m - m) ...(cong (n+) $ sym $ minusSelfZero m)
          ~~ (n + m) - m ...(plusMinusAssociative _ _ _)
          ~~ (m + n) - m ...(cong (\x => x - m) $ plusCommutative _ _)
          ~~ m + (n - m) ...(sym $ plusMinusAssociative _ _ _)

----------------------------
-- Multiplication

||| Multiplying a negative number with a positive number
||| yields a negative number.
export
0 multNegativeRightLT0 : (m,n : Integer) -> 0 < m -> n < 0 -> m * n < 0
multNegativeRightLT0 m n x y =
  replace' (< 0)
    (negMultNegRight _ _)
    ( negPositiveNegative (m * neg n)
    $ multGT _ _ x (negNegativePositive n y))

||| Multiplying a negative number with a positive number
||| yields a negative number.
export
0 multNegativeLeftLT0 : (m,n : Integer) -> m < 0 -> 0 < n -> m * n < 0
multNegativeLeftLT0 m n x y =
  replace' (< 0)
    (multCommutative _ _)
    (multNegativeRightLT0 n m y x)

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

||| For positive `n` and positive `d`, `d * (div n d + 1)` is
||| greater than `n`.
export
0 multDivPlusOneGT : (n,d : Integer) -> (0 < d) -> d * (div n d + 1) > n
multDivPlusOneGT n d dgt0 =
  let -- d * div n d + mod n d === n
      law = lawDivMod n d $ Right dgt0
      -- d * div n d + d > d * div n d + mod n d
      res1 = plusGT (mod n d) d (d * div n d) (snd $ modLT n d dgt0)
      -- d * div n d + d > n
      res2 = replace' (< d * div n d + d) law res1
   in replace' (n <) lemma res2
  where lemma : d * div n d + d === d * (div n d + 1)
        lemma = Calc $
          |~ d * div n d + d
          ~~ d * div n d + d * 1 ...(cong (d * div n d +) $ sym $ multOneRightNeutral d)
          ~~ d * (div n d + 1)   ...(sym $ leftDistributive _ _ _)

||| For positive `n` and positive `d`, `d * div n d` is
||| not less than `n`.
export
0 multDivLTE : (n,d : Integer) -> (0 < d) -> d * div n d <= n
multDivLTE n d dgt0 =
  let -- d * div n d + mod n d === n
      law = lawDivMod n d $ Right dgt0
      -- 0 <= mod n d
      res1 = fst $ modLT n d dgt0
      -- d * div n d <= d * div n d + mod n d
      res2 = plusNonNegativeGTE (d * div n d) (mod n d) res1
   in ?muumu

-- ||| For non-negative `n` and positive `d`, `div n d` is non-negative.
-- export
-- 0 divPositiveGTE0 : (n,d : Integer) -> (0 <= n) -> (0 < d) -> div n d >= 0
-- divPositiveGTE0 n d x y = assert_total $ case comp 0 (div n d) of
--   LT z _ _ => Left z
--   EQ _ z _ => Right z
--
--   -- x < 0 => x * d + y < y < n
--   GT _ _ z =>
--     let xdy_lt_n = trans (multNegativeRightLT0 _ _ y z)
--     in ?foosdl_2
--
--
-- ||| For non-negative `n` and positive `d`, `div n d` is not greater
-- ||| than `n`.
-- export
-- 0 divPositiveLTE : (n,d : Integer) -> (0 <= n) -> (0 < d) -> div n d <= n
-- divPositiveLTE n d x y = assert_total $ case comp (div n d) n of
--   LT z _ _ => Left z
--   EQ _ z _ => Right z
--   GT _ _ z => void (EQ_not_GT {lt = (<)} (lawDivMod n d $ Right y) ?fooooooooo)
--
-- export
-- 0 div0 : (d : Integer) -> (0 < d) -> div 0 d === 0
-- div0 d x = assert_total $ case comp (div 0 d) 0 of
--   EQ _ y _ => y
--   GT _ _ y => void (EQ_not_GT (lawDivMod 0 d $ Right x) $ plusPositiveGT0 _ _ (multGT _ _ x y) ?p2)
--   LT y _ _ => ?dd0_0
--
--
-- export
-- 0 mod0 : (n : Integer) -> 0 < n -> mod 0 n === 0
-- mod0 n x =
--   Calc $
--     |~ mod 0 n
--     ~~ 0 - n * div 0 n ...(solvePlusLeft $ lawDivMod 0 n ?fooo)
--     ~~ 0 - n * 0       ...(cong (\x => 0 - n * x) $ div0 n x)
--     ~~ 0 - 0           ...(cong (\x => 0 - x) $ multZeroRightAbsorbs _)
--     ~~ 0               ...(minusSelfZero 0)

-- export
-- 0 divGT0 : (m,n : Integer) -> (0 <= m

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

-- public export
-- record Middle (m,n : Integer) where
--   constructor MkMiddle
--   value  : Integer
--   0 isMiddle : value === m + div (n - m) 2
--   0 gtem     : m <= value
--   0 ltn      : n >  value
--
-- export
-- middle : (m,n : Integer) -> (0 prf : m < n) => Middle m n
-- middle m n = MkMiddle {
--     value    = m + div (n - m) 2
--   , isMiddle = Refl
--   , gtem     = ?foo
--   , ltn      = ?bar
--   }
--
-- ||| The square root of a non-negative integer `n` is the
-- ||| unique integer `v` with `v >= 0`, `v * v <= n`,
-- ||| and `(v + 1) * (v + 1) > n`.
-- public export
-- record Sqrt (n : Integer) where
--   constructor MkSqrt
--   value : Integer
--   0 nonNegative : 0 <= value
--   0 ltn         : value * value <= n
--   0 gtn         : (value + 1) * (value + 1) > n
--
-- ||| Computes the integer square root of a non-negative integer
-- ||| using a binary search.
-- export
-- sqrt : (n : Integer) -> (0 prf : 0 <= n) => Sqrt n
-- sqrt n = case comp 0 n of
--   GT _ _ x => void $ LT_not_GTE x prf
--   EQ _ x _ => replace' Sqrt x (MkSqrt 0 %search %search %search)
--   LT x _ _ => case comp 1 n of
--     EQ _ y _ => replace' Sqrt y (MkSqrt 1 %search %search %search)
--     GT _ _ y => void (GT_not_LTE y $ oneAfterZero n x)
--     LT y _ _ => ?foo_0
