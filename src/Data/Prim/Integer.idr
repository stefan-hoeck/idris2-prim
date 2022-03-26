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
Total Integer (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

replace' : (0 p : a -> Type) -> (0 _ : x = y) -> p x -> p y
replace' p prf px = replace {p} prf px

derive :  {0 a,b : Type}
       -> (x : a)
       -> FastDerivation a b
       -> b
derive x z = case Calc z of Refl => x

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
0 modNegEQ : (n,d : Integer) -> d < 0 -> mod n d === mod n (neg d)
modNegEQ n d x = strictLT x unsafeRefl

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
  derive (plusGT k m n lt) $
   |~ (n + k < n + m)
   ~~ (n + k < m + n) ...(cong (n+k <) $ plusCommutative n m)
   ~~ (k + n < m + n) ...(cong (< m+n) $ plusCommutative n k)

||| The result of adding a positive number to `m` is strictly greater
||| than `m`.
export
0 plusPositiveGT : (m,n : Integer) -> 0 < n -> m < m + n
plusPositiveGT m n lt =
  derive (plusGT 0 n m lt) $
    |~ (m + 0 < m + n)
    ~~ (m < m + n) ...(cong (< m + n) $ plusZeroRightNeutral m)

||| The result of adding a non-negative number to `m` is not less
||| than `m`.
export
0 plusNonNegativeGTE : (m,n : Integer) -> 0 <= n -> m <= m + n
plusNonNegativeGTE m n (Left x) = Left $ plusPositiveGT m n x
plusNonNegativeGTE m n (Right x) =
  Right $ Calc $
    |~ m
    ~~ m + 0 ..<(plusZeroRightNeutral m)
    ~~ m + n ...(cong (m +) x)

||| The result of adding a negative number to `m` is strictly less
||| than `m`.
export
0 plusNegativeLT : (m,n : Integer) -> n < 0 -> m > m + n
plusNegativeLT m n lt =
  derive (plusGT n 0 m lt) $
    |~ (m + n < m + 0)
    ~~ (m + n < m) ...(cong (m+n <) $ plusZeroRightNeutral m)

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
0 solvePlusRightGT : (m,n : Integer) -> m < m + n -> 0 < n
solvePlusRightGT m n lt = case comp 0 n of
  LT x _    _ => x
  EQ _ Refl _ => void (LT_not_EQ lt (sym $ plusZeroRightNeutral m))
  GT _ _    x => void (LT_not_GT lt $ plusNegativeLT m n x)

||| From `m < n + m` follows `n > 0`.
export
0 solvePlusLeftGT : (m,n : Integer) -> m < n + m -> 0 < n
solvePlusLeftGT m n lt =
  solvePlusRightGT m n $ derive lt $
    |~ m < n + m
    ~~ m < m + n ...(cong (m <) $ plusCommutative n m)

||| From `m > m + n` follows `n < 0`.
export
0 solvePlusRightLT : (m,n : Integer) -> m > m + n -> n < 0
solvePlusRightLT m n lt = case comp 0 n of
  LT x _    _ => void (LT_not_GT lt $ plusPositiveGT m n x)
  EQ _ Refl _ => void (GT_not_EQ lt (sym $ plusZeroRightNeutral m))
  GT _ _    x => x

||| From `m > n + m` follows `n < 0`.
export
0 solvePlusLeftLT : (m,n : Integer) -> m > n + m -> 0 > n
solvePlusLeftLT m n lt =
  solvePlusRightLT m n $ derive lt $
    |~ m > n + m
    ~~ m > m + n ...(cong (m >) $ plusCommutative n m)

||| From `0 < m + 1` follows `0 <= m`.
export
0 solvePlusOneRightGT0 : (m : Integer) -> 0 < m + 1 -> 0 <= m
solvePlusOneRightGT0 m lt = case oneAfterZero (m+1) lt of
  Left x  => Left $ solvePlusLeftGT 1 m x
  Right x => Right $ sym $ solvePlusZeroLeft $ sym x

||| From `0 < 1 + m` follows `0 <= m`.
export
0 solvePlusOneLeftGT0 : (m : Integer) -> 0 < 1 + m -> 0 <= m
solvePlusOneLeftGT0 m lt =
  solvePlusOneRightGT0 m $ derive lt $
    |~ 0 < 1 + m
    ~~ 0 < m + 1 ...(cong (0 <) $ plusCommutative 1 m)


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
minusSmallerPositive m n lt = solvePlusRightGT m (n - m) (replace' (m <) lemma lt)
  where lemma : n === m + (n - m)
        lemma = Calc $
          |~ n
          ~~ n + 0       ..<(plusZeroRightNeutral n)
          ~~ n + (m - m) ..<(cong (n+) $ minusSelfZero m)
          ~~ (n + m) - m ...(plusMinusAssociative _ _ _)
          ~~ (m + n) - m ...(cong (\x => x - m) $ plusCommutative _ _)
          ~~ m + (n - m) ..<(plusMinusAssociative _ _ _)

----------------------------
-- Multiplication

||| Multiplying a negative number with a positive number
||| yields a negative number.
export
0 multPosNegLT0 : (m,n : Integer) -> 0 < m -> n < 0 -> m * n < 0
multPosNegLT0 m n x y =
  replace' (< 0)
    (negMultNegRight _ _)
    ( negPositiveNegative (m * neg n)
    $ multPosPosGT0 _ _ x (negNegativePositive n y))

||| Multiplying a negative number with a positive number
||| yields a negative number.
export
0 multNegPosLT0 : (m,n : Integer) -> m < 0 -> 0 < n -> m * n < 0
multNegPosLT0 m n x y =
  replace' (< 0)
    (multCommutative _ _)
    (multPosNegLT0 n m y x)

||| Multiplying two negative numbers yields a positive number.
export
0 multNegNegGT0 : (m,n : Integer) -> m < 0 -> n < 0 -> 0 < m * n
multNegNegGT0 m n x y =
  let negm_pos = negNegativePositive m x
      negn_pos = negNegativePositive n y
   in derive (multPosPosGT0 (neg m) (neg n) negm_pos negn_pos) $
        |~ 0 < neg m * neg n
        ~~ 0 < m * n         ...(cong (0 <) $ negMultNeg m n)

||| From `m * n === 0` follows `m === 0` or `n === 0`
export
0 solveMultZero :  (m,n : Integer)
                -> m * n === 0
                -> Either (m === 0) (n === 0)
solveMultZero m n p = case (comp 0 m, comp 0 n) of
  (EQ _ x _, _       ) => Left $ sym x
  (_       , EQ _ x _) => Right $ sym x
  (LT x _ _, LT y _ _) => void $ GT_not_EQ (multPosPosGT0 m n x y) p
  (GT _ _ x, LT y _ _) => void $ LT_not_EQ (multNegPosLT0 m n x y) p
  (LT x _ _, GT _ _ y) => void $ LT_not_EQ (multPosNegLT0 m n x y) p
  (GT _ _ x, GT _ _ y) => void $ GT_not_EQ (multNegNegGT0 m n x y) p

||| From `m * n > 0` follows `m > 0` and `n > 0`
||| or `m < 0` and `n < 0`.
export
0 solveMultPos :  (m,n : Integer)
                -> 0 < m * n
                -> Either (m > 0, n > 0) (m < 0, n < 0)
solveMultPos m n p = case (comp m 0, comp n 0) of
  (LT x _ _, LT y _ _) => Right (x,y)
  (GT _ _ x, GT _ _ y) => Left (x,y)

  (GT _ _ x, LT y _ _) => void $ LT_not_GT (multPosNegLT0 m n x y) p
  (LT x _ _, GT _ _ y) => void $ LT_not_GT (multNegPosLT0 m n x y) p
  (EQ _ x _, _       ) => void $ EQ_not_GT (multZeroAbsorbs m n (Left x)) p
  (_       , EQ _ x _) => void $ EQ_not_GT (multZeroAbsorbs m n (Right x)) p

||| From `m * n < 0` follows `m > 0` and `n < 0`
||| or `m < 0` and `n > 0`.
export
0 solveMultNeg :  (m,n : Integer)
                -> 0 > m * n
                -> Either (m < 0, n > 0) (m > 0, n < 0)
solveMultNeg m n p = case (comp m 0, comp n 0) of
  (GT _ _ x, LT y _ _) => Right (x,y)
  (LT x _ _, GT _ _ y) => Left (x,y)

  (LT x _ _, LT y _ _) => void $ GT_not_LT (multNegNegGT0 m n x y) p
  (GT _ _ x, GT _ _ y) => void $ GT_not_LT (multPosPosGT0 m n x y) p
  (EQ _ x _, _       ) => void $ EQ_not_LT (multZeroAbsorbs m n (Left x)) p
  (_       , EQ _ x _) => void $ EQ_not_LT (multZeroAbsorbs m n (Right x)) p

||| From `0 < m` and `0 < m * n` follows `0 < n`.
export
0 solveMultPosLeftGT0 : (m,n : Integer) -> 0 < m -> 0 < m * n -> 0 < n
solveMultPosLeftGT0 m n x y = case solveMultPos m n y of
  Left z  => snd z
  Right z => void $ GT_not_LT x (fst z)

||| From `0 < m` and `0 < n * m` follows `0 < n`.
export
0 solveMultPosRightGT0 : (m,n : Integer) -> 0 < m -> 0 < n * m -> 0 < n
solveMultPosRightGT0 m n x y = case solveMultPos n m y of
  Left z  => fst z
  Right z => void $ GT_not_LT x (snd z)

||| From `0 > m` and `0 < m * n` follows `0 > n`.
export
0 solveMultNegLeftGT0 : (m,n : Integer) -> 0 > m -> 0 < m * n -> 0 > n
solveMultNegLeftGT0 m n x y = case solveMultPos m n y of
  Right z => snd z
  Left z  => void $ GT_not_LT x (fst z)

||| From `0 > m` and `0 < n * m` follows `0 > n`.
export
0 solveMultNegRightGT0 : (m,n : Integer) -> 0 > m -> 0 < n * m -> 0 > n
solveMultNegRightGT0 m n x y = case solveMultPos n m y of
  Right z => fst z
  Left z  => void $ GT_not_LT x (snd z)

||| From `0 < m` and `0 > m * n` follows `0 > n`.
export
0 solveMultPosLeftLT0 : (m,n : Integer) -> 0 < m -> 0 > m * n -> 0 > n
solveMultPosLeftLT0 m n x y = case solveMultNeg m n y of
  Right z => snd z
  Left z  => void $ GT_not_LT x (fst z)

||| From `0 < m` and `0 > n * m` follows `0 > n`.
export
0 solveMultPosRightLT0 : (m,n : Integer) -> 0 < m -> 0 > n * m -> 0 > n
solveMultPosRightLT0 m n x y = case solveMultNeg n m y of
  Left z  => fst z
  Right z => void $ LT_not_GT x $ snd z

||| From `0 > m` and `0 > m * n` follows `0 < n`.
export
0 solveMultNegLeftLT0 : (m,n : Integer) -> 0 > m -> 0 > m * n -> 0 < n
solveMultNegLeftLT0 m n x y = case solveMultNeg m n y of
  Left z  => snd z
  Right z => void $ GT_not_LT x (fst z)

||| From `0 > m` and `0 > n * m` follows `0 < n`.
export
0 solveMultNegRightLT0 : (m,n : Integer) -> 0 > m -> 0 > n * m -> 0 < n
solveMultNegRightLT0 m n x y = case solveMultNeg n m y of
  Right z => fst z
  Left z  => void $ GT_not_LT x (snd z)

||| From `0 < m` and `0 === m * n` follows `0 === n`.
export
0 solveMultPosLeftEQ0 : (m,n : Integer) -> 0 < m -> m * n === 0 -> n === 0
solveMultPosLeftEQ0 m n x y = case solveMultZero m n y of
  Right z => z
  Left z  => void $ GT_not_EQ x z

||| From `0 < m` and `0 === n * m` follows `0 === n`.
export
0 solveMultPosRightEQ0 : (m,n : Integer) -> 0 < m -> n * m === 0 -> n === 0
solveMultPosRightEQ0 m n x y = case solveMultZero n m y of
  Left z  => z
  Right z => void $ GT_not_EQ x z

||| From `0 > m` and `0 === m * n` follows `0 === n`.
export
0 solveMultNegLeftEQ0 : (m,n : Integer) -> 0 > m -> m * n === 0 -> n === 0
solveMultNegLeftEQ0 m n x y = case solveMultZero m n y of
  Right z => z
  Left z  => void $ LT_not_EQ x z

||| From `0 > m` and `0 === n * m` follows `0 === n`.
export
0 solveMultNegRightEQ0 : (m,n : Integer) -> 0 > m -> n * m === 0 -> n === 0
solveMultNegRightEQ0 m n x y = case solveMultZero n m y of
  Left z  => z
  Right z => void $ LT_not_EQ x z

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
  let law = cong (d * div n d + d >) $ lawDivMod n d (Right dgt0)
   in derive (plusGT (mod n d) d (d * div n d) (snd $ modLT n d dgt0)) $
        |~ d * div n d + d > d * div n d + mod n d
        ~~ d * div n d + d   > n ...law
        ~~ d * (div n d + 1) > n ...(cong (> n) $ multPlusSelf _ _)

||| For positive `n` and positive `d`, `d * div n d` is
||| not less than `n`.
export
0 multDivLTE : (n,d : Integer) -> (0 < d) -> d * div n d <= n
multDivLTE n d dgt0 =
  let law = lawDivMod n d $ Right dgt0
   in derive (plusNonNegativeGTE _ _ (fst $ modLT n d dgt0)) $
        |~ d * div n d <= d * div n d + mod n d
        ~~ d * div n d <= n ...(cong (d * div n d <=) $ law)

||| For non-negative `n` and positive `d`, `div n d` is non-negative.
export
0 divNonNegativeGTE0 : (n,d : Integer) -> 0 <= n -> 0 < d -> div n d >= 0
divNonNegativeGTE0 n d x y =
  let gtn = trans_LTE_LT x $ multDivPlusOneGT n d y
      gt0 = solveMultPosLeftGT0 _ _ y gtn
   in solvePlusOneRightGT0 _ gt0

||| For non-negative `n` and positive `d`, `mod n d <= n` holds.
export
0 modNonNegativeLTE : (n,d : Integer) -> 0 <= n -> 0 < d -> mod n d <= n
modNonNegativeLTE n d x y =
  let p1 = solvePlusLeft $ lawDivMod n d $ Right y
   in ?foo

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
--   GT _ _ y => void (EQ_not_GT (lawDivMod 0 d $ Right x) $ plusPositiveGT0 _ _ (multPosPosGT0 _ _ x y) ?p2)
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
