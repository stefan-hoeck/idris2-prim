module Data.Prim.Bits8

import public Data.Dec0
import public Data.DPair
import public Data.Trichotomous

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

strictRefl : (0 prf : a === b) -> Lazy c -> c
strictRefl Refl x = x

0 unsafeRefl : a === b
unsafeRefl = believe_me $ Refl {x = a}

--------------------------------------------------------------------------------
--          EQ
--------------------------------------------------------------------------------

||| Proof that `m == n` equals `True`
export
data (==) : (m,n : Bits8) -> Type where
  IsEQ : (0 prf : (m == n) === True) -> m == n

||| Constructor for `(==)`.
|||
||| This comes with a `%hint` pragma so values of type
||| `m == n` can be derived at compile time if both `m` and `n`
||| are known.
export %hint
0 eq : (m == n) === True -> m == n
eq prf = IsEQ prf

||| Extractor for `(==)`.
export
0 runEQ : m == n -> (m == n) === True
runEQ (IsEQ prf) = prf

namespace EQ

  ||| We don't trust arbitrary values of type `m == n`,
  ||| so we use this when crafting magical ones.
  export
  strict : (0 _ : m == n) -> Lazy c -> c
  strict prf = strictRefl (runEQ prf)

  ||| Decide on `(==)`.
  public export
  decide : (m,n : Bits8) -> Dec0 (m == n)
  decide m n = case test (m == n) of
    Yes0 prf   => Yes0 $ IsEQ prf
    No0 contra => No0 $ \(IsEQ prf) => contra prf

  ||| `(==)` is substitutive.
  export
  elim : (0 p : Bits8 -> Type) -> (0 prf : m == n) -> p m -> p n
  elim _ prf y = strict prf $ believe_me y

  ||| `(==)` implies propositional equality.
  export
  0 reflect : m == n -> m === n
  reflect prf = elim (m ===) prf Refl

  ||| `(==)` is reflective.
  export
  0 refl : m == m
  refl = IsEQ unsafeRefl

  ||| `(==)` is symmetric.
  export
  0 sym : m == n -> n == m
  sym prf = elim (== m) prf refl

  ||| `(==)` is transitive.
  export
  0 trans : k == m -> m == n -> k == n
  trans p q = elim (== n) (sym p) q

--------------------------------------------------------------------------------
--          NEQ
--------------------------------------------------------------------------------

||| Proof that `m == n` equals `False`
export
data (/=) : (m,n : Bits8) -> Type where
  IsNEQ : (0 prf : (m == n) === False) -> m /= n

||| Constructor for `(/=)`.
|||
||| This comes with a `%hint` pragma so values of type
||| `m /= n` can be derived at compile time if both `m` and `n`
||| are known.
export %hint
0 neq : (m == n) === False -> m /= n
neq prf = IsNEQ prf

||| Extractor for `(==)`.
export
0 runNEQ : m /= n -> (m == n) === False
runNEQ (IsNEQ prf) = prf

namespace NEQ

  ||| We don't trust arbitrary values of type `m /= n`,
  ||| so we use this when crafting magical ones.
  export
  strict : (0 _ : m /= n) -> Lazy c -> c
  strict prf = strictRefl (runNEQ prf)

  ||| Decide on `(/=)`.
  public export
  decide : (m,n : Bits8) -> Dec0 (m /= n)
  decide m n = case testNot (m == n) of
    Yes0 prf   => Yes0 $ IsNEQ prf
    No0 contra => No0 $ \(IsNEQ prf) => contra prf

  ||| `m == n` implies `Not (m /= n)`.
  export
  0 EQ_not_NEQ : m == n -> Not (m /= n)
  EQ_not_NEQ (IsEQ x) (IsNEQ y) = absurd (trans (sym x) y)

  ||| `m /= n` implies `Not (m == n)`.
  export
  0 NEQ_not_EQ : m /= n -> Not (m == n)
  NEQ_not_EQ = flip EQ_not_NEQ

  ||| `Not (m == n)` implies `m /= n`.
  export
  0 Not_EQ_to_NEQ : Not (m == n) -> m /= n
  Not_EQ_to_NEQ f = IsNEQ $ notTrueImpliesFalse (m == n) (\p => f $ IsEQ p)

  ||| `Not (m /= n)` implies `m == n`.
  export
  0 Not_NEQ_to_EQ : Not (m /= n) -> m == n
  Not_NEQ_to_EQ f = IsEQ $ notFalseImpliesTrue (m == n) (\p => f $ IsNEQ p)

  ||| `(==)` is symmetric.
  export
  0 sym : m /= n -> n /= m
  sym prf = Not_EQ_to_NEQ (NEQ_not_EQ $ sym prf)

  ||| `k == m` and `m /= n` implies `k /= n`.
  0 trans_EQ_NEQ : k == m -> m /= n -> k /= n
  trans_EQ_NEQ p q = elim (/= n) (sym p) q

  ||| `k == m` and `m /= n` implies `k /= n`.
  0 trans_NEQ_EQ : k /= m -> m == n -> k /= n
  trans_NEQ_EQ p q = elim (k /=) q p

--------------------------------------------------------------------------------
--          LT
--------------------------------------------------------------------------------

||| Proof that `m < n` equals `True`.
export
data (<) : (m,n : Bits8) -> Type where
  IsLT : (0 prf : (m < n) === True) -> m < n

||| Constructor for (<).
|||
||| This comes with a `%hint` pragma so values of type
||| `m < n` can be derived at compile time if both `m` and `n`
||| are known.
export %hint
0 lt : (m < n) === True -> m < n
lt prf = IsLT prf

||| Extractor for (<).
export
0 runLT : m < n -> (m < n) === True
runLT (IsLT prf) = prf

namespace LT

  ||| Decide on `(<)`.
  public export
  decide : (m,n : Bits8) -> Dec0 (m < n)
  decide m n = case test (m < n) of
    Yes0 prf   => Yes0 (IsLT prf)
    No0 contra => No0 $ contra . runLT

  ||| We don't trust arbitrary values of type `m < n`.
  ||| So we use this when crafting magical ones.
  export
  strict : (0 prf : m < n) -> Lazy c -> c
  strict prf = strictRefl (runLT prf)

  ||| `(<)` is transitive.
  export
  0 trans : k < m -> m < n -> k < n
  trans p q = strict p $ strict q $ IsLT unsafeRefl

  ||| `(<)` is irreflexive.
  export
  0 irrefl : Not (a < a)
  irrefl prf = strict prf
             $ assert_total
             $ idris_crash "IMPOSSIBLE: LT on Bits8 is irreflexible."

||| `n > m` is an alias for `m < n`.
public export
0 (>) : (m,n : Bits8) -> Type
m > n = n < m

||| `m > n` implies `Not (m < n)`
export
0 GT_not_LT : m > n -> Not (m < n)
GT_not_LT p1 p2 = irrefl (trans p1 p2)

||| `m < n` implies `Not (m > n)`
export
0 LT_not_GT : m < n -> Not (m > n)
LT_not_GT p1 p2 = irrefl (trans p1 p2)

||| `k < m` and `m == n` implies `k < n`
export
0 trans_LT_EQ : k < m -> m == n -> k < n
trans_LT_EQ p q = elim (k <) q p

||| `k == m` and `m < n` implies `k < n`
export
0 trans_EQ_LT : k == m -> m < n -> k < n
trans_EQ_LT p q = elim (< n) (sym p) q

||| `m == n` implies `Not (m < n)`
export
0 EQ_not_LT : m == n -> Not (m < n)
EQ_not_LT x y = irrefl (trans_LT_EQ y (sym x))

||| `m == n` implies `Not (m > n)`
export
0 EQ_not_GT : m == n -> Not (m > n)
EQ_not_GT x y = irrefl (trans_LT_EQ y x)

||| `m < n` implies `Not (m == n)`
export
0 LT_not_EQ : m < n -> Not (m == n)
LT_not_EQ = flip EQ_not_LT

||| `m < n` implies `Not (m == n)`
export
0 GT_not_EQ : m > n -> Not (m == n)
GT_not_EQ = flip EQ_not_GT

||| `m < n` implies `m /= n`
export
0 LT_to_NEQ : m < n -> m /= n
LT_to_NEQ = Not_EQ_to_NEQ . LT_not_EQ

||| `m > n` implies `m /= n`
export
0 GT_to_NEQ : m > n -> m /= n
GT_to_NEQ = sym . LT_to_NEQ

--------------------------------------------------------------------------------
--          LTE
--------------------------------------------------------------------------------

||| Proof that `m < n` equals `True` or `m == n` equals `True`.
public export
data (<=) : (m,n : Bits8) -> Type where
  MkLT : (0 prf : m < n) -> m <= n
  MkEQ : (0 prf : m == n) -> m <= n

||| 0xff is the upper bound of Bits8
export
0 lteMax : n <= 0xff
lteMax = case n of
  0xff => MkEQ refl
  _    => MkLT $ IsLT unsafeRefl

||| 0 is the lower bound of Bits8
export
0 zeroLTE : 0 <= n
zeroLTE = case n of
  0 => MkEQ refl
  _ => MkLT $ IsLT unsafeRefl

namespace LTE

  ||| Decide on `(<=)`.
  public export
  decide : (m,n : Bits8) -> Dec0 (m <= n)
  decide m n = case EQ.decide m n of
    Yes0 eq => Yes0 $ MkEQ eq
    No0  c1 => case LT.decide m n of
      Yes0 lt => Yes0 $ MkLT lt
      No0 c2  => No0 $ \case (MkEQ prf) => c1 prf
                             (MkLT prf) => c2 prf

  ||| `(<=)` is reflective.
  export
  0 refl : m <= m
  refl = MkEQ refl

  ||| `(<=)` is transitive.
  export
  0 trans : k <= m -> m <= n -> k <= n
  trans (MkLT x) (MkLT y) = MkLT $ trans x y
  trans (MkLT x) (MkEQ y) = MkLT $ trans_LT_EQ x y
  trans (MkEQ x) (MkLT y) = MkLT $ trans_EQ_LT x y
  trans (MkEQ x) (MkEQ y) = MkEQ $ trans x y

  ||| `(k <= m)` and `(m < n)` implies `(k < n)`
  export
  0 trans_LTE_LT : k <= m -> m < n -> k < n
  trans_LTE_LT (MkLT x) y = trans x y
  trans_LTE_LT (MkEQ x) y = trans_EQ_LT x y

  ||| `(k < m)` and `(m <= n)` implies `(k < n)`
  export
  0 trans_LT_LTE : k < m -> m <= n -> k < n
  trans_LT_LTE x (MkLT y) = trans x y
  trans_LT_LTE x (MkEQ y) = trans_LT_EQ x y

  ||| `(k <= m)` and `(m == n)` implies `(k < n)`
  export
  0 trans_LTE_EQ : k <= m -> m == n -> k <= n
  trans_LTE_EQ lte eq = trans lte (MkEQ eq)

  ||| `(k == m)` and `(m <= n)` implies `(k < n)`
  export
  0 trans_EQ_LTE : k == m -> m <= n -> k <= n
  trans_EQ_LTE eq lte = trans (MkEQ eq) lte

  ||| `(<=)` is antisymmetric.
  export
  0 antisym : m <= n -> n <= m -> m == n
  antisym (MkEQ x) _        = x
  antisym (MkLT x) (MkEQ y) = sym y
  antisym (MkLT x) (MkLT y) = void (LT_not_GT x y)

||| `n >= m` is an alias for `m <= n`.
public export
0 (>=) : (m,n : Bits8) -> Type
m >= n = n <= m

--------------------------------------------------------------------------------
--          Di- and Trichotomy
--------------------------------------------------------------------------------

||| Any pair of values of type Bits8 is related either via `(==)` or `(/=)`.
export
dichotomous : (a, b : Bits8) -> Dichotomous (==) (/=) a b
dichotomous a b = case EQ.decide a b of
  Yes0 prf   => MkE prf (EQ_not_NEQ prf)
  No0 contra => MkN contra (Not_EQ_to_NEQ contra)

||| Any pair of values of type Bits8 is related either via `(<)`, `(==)`, `(>)`
export
trichotomous : (a, b : Bits8) -> Trichotomous (<) (==) (>) a b
trichotomous a b = case LT.decide a b of
  Yes0 lt =>  MkLT lt (LT_not_EQ lt) (LT_not_GT lt)
  No0  _  => case EQ.decide a b of
    Yes0 eq => MkEQ (EQ_not_LT eq) eq (EQ_not_GT eq)
    No0  _  =>
      let gt = IsLT unsafeRefl
       in MkGT (GT_not_LT gt) (GT_not_EQ gt) gt

||| From `m /= n` follows `m < n` or `m > n`.
export
NEQ_to_LT_or_GT : (m,n : Bits8) -> m /= n -> Dichotomous (<) (>) m n
NEQ_to_LT_or_GT m n x = case trichotomous m n of
  MkLT y _ g => MkE y g
  MkGT f _ y => MkN f y
  MkEQ _ y _ => void (NEQ_not_EQ x y)

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe integer division
public export
sdiv : (m,n : Bits8) -> (0 prf : n > 0) => Bits8
sdiv m n = div m n

||| Safe modulo
public export
smod : (m,n : Bits8) -> (0 prf : n > 0) => Subset Bits8 (< n)
smod m n = Element (m `mod` n) (IsLT unsafeRefl)
