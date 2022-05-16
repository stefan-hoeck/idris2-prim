||| Axioms and propsitions for primitive types with an
||| `Ord` implementation.
module Data.Prim.Ord

import public Data.Trichotomy

%default total

||| Similar to `Either` but with erased fields.
public export
data Either0 : Type -> Type -> Type where
  Left0  : (0 v : a) -> Either0 a b
  Right0 : (0 v : b) -> Either0 a b

||| We often don't trust values of type `a === b`, as they might
||| have been magically crafted using `believe_me` or `assert_total`
||| followed by `idris_crash`. If a value of another type follows
||| from a (potentially) magically crafted one, we only want the
||| second value to reduce at compile time, if the first value
||| reduces to `Refl`. Otherwise, we risk blowing up the compiler
||| in an absurd context.
export
strictRefl : (0 prf : a === b) -> Lazy c -> c
strictRefl Refl x = x

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| This interface is a witness that the given primitive type
||| comes with a relation `lt`, with `lt` being a strict total order.
||| We typically define the following aliases
||| (or name the relation accordingly):
|||
|||   `m < n`  := lt m n
|||   `m > n`  := lt n m
|||   `m <= n` := Either (lt m n) (m === n)
|||   `m >= n` := Either (lt n m) (n === m)
|||   `m /= n` := Either (lt m n) (lt n m)
|||
||| The following axioms must hold:
|||   1. (<) is transitive: From `k < m` and `m < n` follows `k < n`.
|||
|||   2. Trichotomy: For all values `m` and `n` exactly one of the
|||      following holds: `m < n`, `m === n`, or `n < m`.
|||
||| It is in the nature of a primitive that we can't proof these axioms
||| in Idris itself. We must therefore assume that they hold on all backends,
||| and it is the responsibility of programmers implementing
||| interface `Total` to make sure that the axioms actually hold.
public export
interface Total (0 a : Type) (0 lt : a -> a -> Type) | lt where
  ||| Axiom I: `<` is transitive.
  0 transLT : {k,m,n : a} -> lt k m -> lt m n -> lt k n

  ||| Axiom II: Trichotomy of `<`, `===`, and `>`.
  trichotomy : (m,n : a) -> Trichotomy lt m n

||| Tests if the first value is strictly less than the second or not
export
testLT : Total a lt => (x,y : a) -> Either0 (lt x y) (Either (lt y x) (y === x))
testLT x y = case trichotomy {lt} x y of
  LT p _ _ => Left0 p
  EQ _ p _ => Right0 (Right $ sym p)
  GT _ _ p => Right0 (Left p)

||| Tests if the first value is strictly greater than the second or not
export
testGT : Total a lt => (x,y : a) -> Either0 (lt y x) (Either (lt x y) (x === y))
testGT x y = case trichotomy {lt} x y of
  GT _ _ p => Left0 p
  LT p _ _ => Right0 (Left p)
  EQ _ p _ => Right0 (Right p)

||| Tests if the two values are provably equal or not
export
testEQ : Total a lt => (x,y : a) -> Either0 (x === y) (Either (lt x y) (lt y x))
testEQ x y = case trichotomy {lt} x y of
  EQ _ p _ => Left0 p
  LT p _ _ => Right0 (Left p)
  GT _ _ p => Right0 (Right p)

--------------------------------------------------------------------------------
--          Corollaries
--------------------------------------------------------------------------------

||| `<` is irreflexive.
export
0 irrefl : Total a lt => Not (lt m m)
irrefl x = case trichotomy m m of
  LT y _ f => f y
  EQ f _ _ => f x
  GT f _ y => f y

--------------------------------------------------------------------------------
--          Transitivities
--------------------------------------------------------------------------------

namespace LT

  ||| This is an alias for `transLT`
  export
  0 trans : Total a lt => lt k m -> lt m n -> lt k n
  trans = transLT

||| `k === m` and `m /= n` implies `k /= n`.
export
0 trans_EQ_NEQ :  Total a lt
               => k === m
               -> Either (lt m n) (lt n m)
               -> Either (lt k n) (lt n k)
trans_EQ_NEQ eqv neq  = rewrite eqv in neq

||| `k === m` and `m /= n` implies `k /= n`.
export
0 trans_NEQ_EQ :  Total a lt
               => Either (lt k m) (lt m k)
               -> m === n
               -> Either (lt k n) (lt n k)
trans_NEQ_EQ neq eqv = rewrite (sym eqv) in neq

||| `k < m` and `m === n` implies `k < n`
export
0 trans_LT_EQ : Total a lt => lt k m -> m === n -> lt k n
trans_LT_EQ p eqv = rewrite sym eqv in p

||| `k === m` and `m < n` implies `k < n`
export
0 trans_EQ_LT : Total a lt => k === m -> lt m n -> lt k n
trans_EQ_LT eqv q = rewrite eqv in q

||| `k <= m` and `m < n` implies `k < n`
export
0 trans_LTE_LT : Total a lt => Either (lt k m) (k === m) -> lt m n -> lt k n
trans_LTE_LT x y = either (`trans` y) (`trans_EQ_LT` y) x

||| `k < m` and `m <= n` implies `k < n`
export
0 trans_LT_LTE : Total a lt => lt k m -> Either (lt m n) (m === n) -> lt k n
trans_LT_LTE x = either (trans x) (trans_LT_EQ x)

||| `k > m` and `m === n` implies `k > n`
export
0 trans_GT_EQ : Total a lt => lt m k -> m === n -> lt n k
trans_GT_EQ p eqv = rewrite sym eqv in p

||| `k === m` and `m > n` implies `k > n`
export
0 trans_EQ_GT : Total a lt => k === m -> lt n m -> lt n k
trans_EQ_GT eqv q = rewrite eqv in q

||| `k >= m` and `m > n` implies `k > n`
export
0 trans_GTE_GT : Total a lt => Either (lt m k) (m === k) -> lt n m -> lt n k
trans_GTE_GT x y = either (trans y) (\v => trans_EQ_GT (sym v) y) x

||| `k > m` and `m >= n` implies `k > n`
export
0 trans_GT_GTE : Total a lt => lt m k -> Either (lt n m) (n === m) -> lt n k
trans_GT_GTE x (Left y)  = trans y x
trans_GT_GTE x (Right y) = trans_GT_EQ x (sym y)

namespace LTE

  ||| `<=` is reflexive.
  export
  0 refl : Total a lt => Either (lt m m) (m === m)
  refl = Right Refl

  ||| `<=` is transitive.
  export
  0 trans :  Total a lt
          => Either (lt k m) (k === m)
          -> Either (lt m n) (m === n)
          -> Either (lt k n) (k === n)
  trans (Left x)  y         = Left (trans_LT_LTE x y)
  trans (Right x) (Left y)  = Left (trans_EQ_LT x y)
  trans (Right x) (Right y) = Right (trans x y)

  ||| `<=` is antisymmetric.
  export
  0 antisym :  Total a lt
            => Either (lt m n) (m === n)
            -> Either (lt n m) (m === n)
            -> m === n
  antisym (Right x) _         = x
  antisym (Left x)  (Right y) = y
  antisym (Left x)  (Left y)  = void (irrefl $ trans x y)

||| `k <= m` and `m === n` implies `k <= n`
export
0 trans_LTE_EQ :  Total a lt
               => Either (lt k m) (k === m)
               -> m === n
               -> Either (lt k n) (k === n)
trans_LTE_EQ lte eq = trans lte (Right eq)

||| `k === m` and `m <= n` implies `(k <= n)`
export
0 trans_EQ_LTE :  Total a lt
               => k === m
               -> Either (lt m n) (m === n)
               -> Either (lt k n) (k === n)
trans_EQ_LTE eq lte = trans (Right eq) lte

namespace GTE

  ||| `>=` is transitive.
  export
  0 trans :  Total a lt
          => Either (lt m k) (m === k)
          -> Either (lt n m) (n === m)
          -> Either (lt n k) (n === k)
  trans (Left x)  y         = Left (trans_GT_GTE x y)
  trans (Right x) (Left y)  = Left (trans_EQ_GT (sym x) y)
  trans (Right x) (Right y) = Right (trans y x)

  ||| `>=` is antisymmetric.
  export
  0 antisym :  Total a lt
            => Either (lt n m) (m === n)
            -> Either (lt m n) (m === n)
            -> m === n
  antisym (Right x) _         = x
  antisym (Left x)  (Right y) = y
  antisym (Left x)  (Left y)  = void (irrefl $ trans x y)

||| `k >= m` and `m === n` implies `k >= n`
export
0 trans_GTE_EQ :  Total a lt
               => Either (lt m k) (m === k)
               -> m === n
               -> Either (lt n k) (n === k)
trans_GTE_EQ gte eq = trans gte (Right $ sym eq)

||| `k === m` and `m <= n` implies `(k <= n)`
export
0 trans_EQ_GTE :  Total a lt
               => k === m
               -> Either (lt n m) (n === m)
               -> Either (lt n k) (n === k)
trans_EQ_GTE eq gte = trans (Right $ sym eq) gte

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

||| `m < n` implies `Not (m > n)`.
export
0 LT_not_GT : Total a lt => lt m n -> Not (lt n m)
LT_not_GT isLT isGT = case trichotomy m n of
  LT _ _ g => g isGT
  EQ _ _ g => g isGT
  GT f _ _ => f isLT

||| `m < n` implies `Not (m === n)`.
export
0 LT_not_EQ : Total a lt => lt m n -> Not (m === n)
LT_not_EQ isLT isEQ = case trichotomy m n of
  LT _ g _ => g isEQ
  EQ f _ _ => f isLT
  GT _ g _ => g isEQ

||| `m < n` implies `Not (m >= n)`.
export
0 LT_not_GTE : Total a lt => lt m n -> Not (Either (lt n m) (n === m))
LT_not_GTE l = either (LT_not_GT l) (\e => LT_not_EQ l (sym e))

||| `Not (m < n)` implies `m >= n`.
export
0 Not_LT_to_GTE : Total a lt => Not (lt m n) -> Either (lt n m) (n === m)
Not_LT_to_GTE f = case trichotomy m n of
  LT x _ _ => void (f x)
  EQ _ x _ => Right (sym x)
  GT _ _ x => Left x

||| `m === n` implies `Not (m < n)`.
export
0 EQ_not_LT : Total a lt => m === n -> Not (lt m n)
EQ_not_LT = flip LT_not_EQ

||| `m === n` implies `Not (m > n)`.
export
0 EQ_not_GT : Total a lt => m === n -> Not (lt n m)
EQ_not_GT isEQ = EQ_not_LT (sym isEQ)

||| `m === n` implies `Not (m /= n)`.
export
0 EQ_not_NEQ : Total a lt => m === n -> Not (Either (lt m n) (lt n m))
EQ_not_NEQ isEQ = either (EQ_not_LT isEQ) (EQ_not_GT isEQ)

||| `Not (m < n)` implies `m /= n`.
export
0 Not_EQ_to_NEQ : Total a lt => Not (m === n) -> Either (lt m n) (lt n m)
Not_EQ_to_NEQ f = case trichotomy m n of
  LT x _ _ => Left x
  EQ _ x _ => void (f x)
  GT _ _ x => Right x

||| `m > n` implies `Not (m < n)`.
export
0 GT_not_LT : Total a lt => lt n m -> Not (lt m n)
GT_not_LT = LT_not_GT

||| `m > n` implies `Not (m === n)`.
export
0 GT_not_EQ : Total a lt => lt n m -> Not (m === n)
GT_not_EQ = flip EQ_not_GT

||| `m > n` implies `Not (m <= n)`.
export
0 GT_not_LTE : Total a lt => lt n m -> Not (Either (lt m n) (m === n))
GT_not_LTE gt = either (GT_not_LT gt) (GT_not_EQ gt)

||| `Not (m > n)` implies `m <= n`.
export
0 Not_GT_to_LTE : Total a lt => Not (lt n m) -> Either (lt m n) (m === n)
Not_GT_to_LTE f = case trichotomy m n of
  LT x _ _ => Left x
  EQ _ x _ => Right x
  GT _ _ x => void (f x)

||| `m <= n` implies `Not (m > n)`.
export
0 LTE_not_GT : Total a lt => (Either (lt m n) (m === n)) -> Not (lt n m)
LTE_not_GT = either LT_not_GT EQ_not_GT

||| `Not (m <= n)` implies `m > n`.
export
0 Not_LTE_to_GT : Total a lt => Not (Either (lt m n) (m === n)) -> lt n m
Not_LTE_to_GT f = case trichotomy m n of
  LT x _ _ => void (f $ Left x)
  EQ _ x _ => void (f $ Right x)
  GT _ _ x => x

||| `m <= n` and `m >= n` implies `m === n`.
export
0 LTE_and_GTE_to_EQ :  Total a lt
                    => Either (lt m n) (m === n)
                    -> Either (lt n m) (n === m)
                    -> m === n
LTE_and_GTE_to_EQ (Left x)  (Right y) = sym y
LTE_and_GTE_to_EQ (Right x) _         = x
LTE_and_GTE_to_EQ (Left x)  (Left y)  = void (LT_not_GT x y)

||| `m <= n` and `m /= n` implies `m < n`.
export
0 LTE_and_NEQ_to_LT :  Total a lt
                    => Either (lt m n) (m === n)
                    -> Either (lt m n) (lt n m)
                    -> lt m n
LTE_and_NEQ_to_LT (Left x)  _         = x
LTE_and_NEQ_to_LT (Right _) (Left x)  = x
LTE_and_NEQ_to_LT (Right x) (Right y) = void (EQ_not_GT x y)

||| `m /= n` implies `Not (m === n)`.
export
0 NEQ_not_EQ : Total a lt => Either (lt m n) (lt n m) -> Not (m === n)
NEQ_not_EQ = either LT_not_EQ GT_not_EQ

||| `Not (m /= n)` implies `m === n`.
export
0 Not_NEQ_to_EQ : Total a lt => Not (Either (lt m n) (lt n m)) -> m === n
Not_NEQ_to_EQ f = case trichotomy m n of
  LT x _ _ => void (f $ Left x)
  EQ _ x _ => x
  GT _ _ x => void (f $ Right x)

||| `m /= n` and `m <= n` implies `m < n`.
export
0 NEQ_and_LTE_to_LT :  Total a lt
                    => Either (lt m n) (lt n m)
                    -> Either (lt m n) (m === n)
                    -> lt m n
NEQ_and_LTE_to_LT = flip LTE_and_NEQ_to_LT

||| `m /= n` and `m <= n` implies `m < n`.
export
0 NEQ_and_GTE_to_GT :  Total a lt
                    => Either (lt m n) (lt n m)
                    -> Either (lt n m) (n === m)
                    -> lt n m
NEQ_and_GTE_to_GT (Right x) _         = x
NEQ_and_GTE_to_GT (Left _)  (Left y)  = y
NEQ_and_GTE_to_GT (Left x)  (Right y) = void (GT_not_EQ x y)

||| `m >= n` implies `Not (m < n)`.
export
0 GTE_not_LT : Total a lt => Either (lt n m) (n === m) -> Not (lt m n)
GTE_not_LT = either GT_not_LT EQ_not_GT

||| `Not (m >= n)` implies `m < n`.
export
0 Not_GTE_to_LT : Total a lt => Not (Either (lt n m) (n === m)) -> lt m n
Not_GTE_to_LT f = case trichotomy m n of
  LT x _ _ => x
  EQ _ x _ => void (f $ Right (sym x))
  GT _ _ x => void (f $ Left x)

||| `m >= n` and `m <= n` implies `m === n`.
export
0 GTE_and_LTE_to_EQ :  Total a lt
                    => Either (lt n m) (n === m)
                    -> Either (lt m n) (m === n)
                    -> m === n
GTE_and_LTE_to_EQ = flip LTE_and_GTE_to_EQ

||| `m >= n` and `m /= n` implies `m > n`.
export
0 GTE_and_NEQ_to_GT :  Total a lt
                    => Either (lt n m) (n === m)
                    -> Either (lt m n) (lt n m)
                    -> lt n m
GTE_and_NEQ_to_GT = flip NEQ_and_GTE_to_GT
