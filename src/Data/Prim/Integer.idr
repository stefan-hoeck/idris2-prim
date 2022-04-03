module Data.Prim.Integer

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

export
Total Integer (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Ring Solver
--------------------------------------------------------------------------------

public export
record SSInteger (as : List Integer) (s : Sum Integer as) where
  constructor SS
  sum   : Sum Integer as
  0 prf : esum sum === esum s

public export
sumInteger_ : (s : Sum Integer as) -> SSInteger as s
sumInteger_ []           = SS [] Refl
sumInteger_ (T f p :: y) =
  let SS sy py = sumInteger_ y
   in case f of
        0 => SS sy (psum0 py)
        _ => SS (T f p :: sy) (cong ((f * eprod p) +) py)

public export
normInteger : {as : List Integer} -> Expr Integer as -> Sum Integer as
normInteger e = sum $ sumInteger_ $ normalize e

0 pnormInteger :  {as : List Integer}
               -> (e : Expr Integer as)
               -> eval e === esum (normInteger e)
pnormInteger e with (sumInteger_ $ normalize e)
  pnormInteger e | SS sInteger prf = Calc $
    |~ eval e
    ~~ esum (normalize e)  ...(pnormalize e)
    ~~ esum sInteger            ..<(prf)

export
0 solve :  (as : List Integer)
        -> (e1,e2 : Expr Integer as)
        -> (prf : normInteger e1 === normInteger e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normInteger e1) ...(pnormInteger e1)
  ~~ esum (normInteger e2) ...(cong esum prf)
  ~~ eval e2           ..<(pnormInteger e2)

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

-- ----------------------------
-- -- Division
--
-- ||| Safe division.
-- export %inline
-- sdiv : (n,d : Integer) -> (0 prf : d /= 0) => Integer
-- sdiv n d = n `div` d
--
-- ||| Safe modulo.
-- export %inline
-- smod : (n,d : Integer) -> (0 prf : d /= 0) => Integer
-- smod n d = n `mod` d
--
-- ||| For positive `n` and positive `d`, `d * (div n d + 1)` is
-- ||| greater than `n`.
-- export
-- 0 multDivPlusOneGT : (n,d : Integer) -> (0 < d) -> d * (div n d + 1) > n
-- multDivPlusOneGT n d dgt0 =
--   let law = cong (d * div n d + d >) $ lawDivMod n d (Right dgt0)
--    in derive (plusGT (mod n d) d (d * div n d) (snd $ modLT n d dgt0)) $
--         |~ d * div n d + d > d * div n d + mod n d
--         ~~ d * div n d + d   > n ...law
--         ~~ d * (div n d + 1) > n ...(cong (> n) $ multPlusSelf _ _)
--
-- ||| For positive `n` and positive `d`, `d * div n d` is
-- ||| not less than `n`.
-- export
-- 0 multDivLTE : (n,d : Integer) -> (0 < d) -> d * div n d <= n
-- multDivLTE n d dgt0 =
--   let law = lawDivMod n d $ Right dgt0
--    in derive (plusNonNegativeGTE _ _ (fst $ modLT n d dgt0)) $
--         |~ d * div n d <= d * div n d + mod n d
--         ~~ d * div n d <= n ...(cong (d * div n d <=) $ law)
--
-- ||| For non-negative `n` and positive `d`, `div n d` is non-negative.
-- export
-- 0 divNonNegativeGTE0 : (n,d : Integer) -> 0 <= n -> 0 < d -> div n d >= 0
-- divNonNegativeGTE0 n d x y =
--   let gtn = trans_LTE_LT x $ multDivPlusOneGT n d y
--       gt0 = solveMultPosLeftGT0 _ _ y gtn
--    in solvePlusOneRightGT0 _ gt0
--
-- ||| For non-negative `n` and positive `d`, `mod n d <= n` holds.
-- export
-- 0 modNonNegativeLTE : (n,d : Integer) -> 0 <= n -> 0 < d -> mod n d <= n
-- modNonNegativeLTE n d x y =
--   let p1 = solvePlusLeft $ lawDivMod n d $ Right y
--    in ?foo

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
