||| Axioms and propsitions for primitive types with an
||| `Ord` implementation.
module Data.Prim.Ord

import public Data.Trichotomy

%default total

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
||| comes with two relations `lt` and `eq`, with `lt` being a
||| strict total order and `eq` being an equivalence relation.
||| For these, we typically define the following aliases
||| (or name the relations accordingly):
|||
|||   `m < n`  := lt m n
|||   `m > n`  := lt n m
|||   `m == n` := eq m n
|||   `m <= n` := Either (lt m n) (eq m n)
|||   `m >= n` := Either (lt n m) (eq n m)
|||   `m /= n` := Either (lt m n) (lt n m)
|||
||| The following axioms must hold for the two relations:
|||
|||   1. m == n eliminates: From `m == n` follows
|||      `p m -> p n` for all predicates `p`. In particular,
|||      this means that from `m == n` follows propositional
|||      equality (`m === n`).
|||
|||   2. (==) is reflexive: `m == m` holds for all values `m`.
|||
|||   3. (<) is transitive: From `k < m` and `m < n` follows `k < n`.
|||
|||   4. Trichotomy: For all values `m` and `n` exactly one of the
|||      following holds: `m < n`, `m == n`, or `n < m`.
|||
||| It is in the nature of a primitive that we can't proof these axioms
||| in Idris itself. We must therefore assume that they hold on all backends,
||| and it is the responsibility of programmers implementing
||| interface `Strict` to make sure that the axioms actually hold.
|||
||| A note about type inference: Being parameterized by three types,
||| type inference for `Strict` is horrible unless we define a
||| (single) determining parameter. I first chose `a` for this,
||| but that didn't go too well. Since most of the time we are
||| interested in proofs of type `lt` (or related values), using
||| `lt` as the determining parameter works pretty well in most
||| circumstance. Still, be prepared to a times having to be
||| explicit about `lt`, if Idris can't figure it out on its own.
public export
interface Strict (0 a : Type) (0 lt,eq : a -> a -> Type) | lt where
  ||| Axiom I: `==` is substitutive.
  elim :  {0 m,n : a}
       -> (0 p : a -> Type)
       -> (0 prf : eq m n)
       -> p m
       -> p n

  ||| Axiom II: `==` is reflexive.
  0 reflEQ : {m : a} -> eq m m

  ||| Axiom III: `<` is transitive.
  0 transLT : {k,m,n : a} -> lt k m -> lt m n -> lt k n

  ||| Axiom IV: Trichotomy of `<`, `==`, and `>`.
  trichotomy : (m,n : a) -> Trichotomy lt eq m n


swap : Either a b -> Either b a
swap (Left x)  = Right x
swap (Right x) = Left x

--------------------------------------------------------------------------------
--          Corollaries
--------------------------------------------------------------------------------

||| `==` implies propositional equality.
export
0 reflect : Strict a lt eq => eq m n -> m === n
reflect prf = elim {lt} (m ===) prf Refl

||| Propositional equality implies `==`.
export
0 eqFromRefl : Strict a lt eq => m === n -> eq m n
eqFromRefl prf = replace {p = eq m} prf (reflEQ {lt})

||| Propositional equality implies `<=`.
export
0 lteFromRefl : Strict a lt eq => m === n -> Either (lt m n) (eq m n)
lteFromRefl prf = Right $ eqFromRefl {lt} prf

||| Propositional equality implies `>=`.
export
0 gteFromRefl : Strict a lt eq => m === n -> Either (lt n m) (eq n m)
gteFromRefl prf = Right $ eqFromRefl {lt} (sym prf)

namespace EQ

  ||| This is an alias for `reflEQ`.
  export
  0 refl : Strict a lt eq =>  eq m m
  refl = reflEQ {lt}

  ||| `==` is symmetric.
  export
  0 sym : Strict a lt eq => eq m n -> eq n m
  sym prf = elim {lt} (`eq` m) prf (refl {lt})

  ||| `==` is transitive.
  export
  0 trans : Strict a lt eq => eq k m -> eq m n -> eq k n
  trans p q = elim {lt} (`eq` n) (sym {lt} p) q

namespace LT

  ||| `<` is irreflexive.
  export
  0 irrefl : Strict a lt eq => Not (lt m m)
  irrefl x = case trichotomy m m of
    LT y _ f => f y
    EQ f _ _ => f x
    GT f _ y => f y

  ||| This is an alias for `transLT`
  export
  0 trans : Strict a lt eq => lt k m -> lt m n -> lt k n
  trans = transLT

--------------------------------------------------------------------------------
--          Transitivities
--------------------------------------------------------------------------------

||| `k == m` and `m /= n` implies `k /= n`.
export
0 trans_EQ_NEQ :  Strict a lt eq
               => eq k m
               -> Either (lt m n) (lt n m)
               -> Either (lt k n) (lt n k)
trans_EQ_NEQ eqv (Left x)  = Left (elim {lt} (`lt` n) (sym {lt} eqv) x)
trans_EQ_NEQ eqv (Right x) = Right (elim {lt} (lt n) (sym {lt} eqv) x)

||| `k == m` and `m /= n` implies `k /= n`.
export
0 trans_NEQ_EQ :  Strict a lt eq
               => Either (lt k m) (lt m k)
               -> eq m n
               -> Either (lt k n) (lt n k)
trans_NEQ_EQ neq eqv = swap $ trans_EQ_NEQ (sym {lt} eqv) (swap neq)


||| `k < m` and `m == n` implies `k < n`
export
0 trans_LT_EQ : Strict a lt eq => lt k m -> eq m n -> lt k n
trans_LT_EQ p q = elim {lt} (lt k) q p

||| `k == m` and `m < n` implies `k < n`
export
0 trans_EQ_LT : Strict a lt eq => eq k m -> lt m n -> lt k n
trans_EQ_LT p q = elim {lt} (`lt` n) (sym {lt} p) q

||| `k <= m` and `m < n` implies `k < n`
export
0 trans_LTE_LT : Strict a lt eq => Either (lt k m) (eq k m) -> lt m n -> lt k n
trans_LTE_LT (Left x)  y = trans x y
trans_LTE_LT (Right x) y = trans_EQ_LT x y

||| `k < m` and `m <= n` implies `k < n`
export
0 trans_LT_LTE : Strict a lt eq => lt k m -> Either (lt m n) (eq m n) -> lt k n
trans_LT_LTE x (Left y)  = trans x y
trans_LT_LTE x (Right y) = trans_LT_EQ x y

||| `k > m` and `m == n` implies `k > n`
export
0 trans_GT_EQ : Strict a lt eq => lt m k -> eq m n -> lt n k
trans_GT_EQ p q = elim {lt} (`lt` k) q p

||| `k == m` and `m > n` implies `k > n`
export
0 trans_EQ_GT : Strict a lt eq => eq k m -> lt n m -> lt n k
trans_EQ_GT p q = elim {lt} (lt n) (sym {lt} p) q

||| `k >= m` and `m > n` implies `k > n`
export
0 trans_GTE_GT : Strict a lt eq => Either (lt m k) (eq m k) -> lt n m -> lt n k
trans_GTE_GT (Left x)  y = trans y x
trans_GTE_GT (Right x) y = trans_EQ_GT (sym {lt} x) y

||| `k > m` and `m >= n` implies `k > n`
export
0 trans_GT_GTE : Strict a lt eq => lt m k -> Either (lt n m) (eq n m) -> lt n k
trans_GT_GTE x (Left y)  = trans y x
trans_GT_GTE x (Right y) = trans_GT_EQ x (sym {lt} y)

namespace LTE

  ||| `<=` is reflexive.
  export
  0 refl : Strict a lt eq => Either (lt m m) (eq m m)
  refl = Right (refl {lt})

  ||| `<=` is transitive.
  export
  0 trans :  Strict a lt eq
          => Either (lt k m) (eq k m)
          -> Either (lt m n) (eq m n)
          -> Either (lt k n) (eq k n)
  trans (Left x)  y         = Left (trans_LT_LTE x y)
  trans (Right x) (Left y)  = Left (trans_EQ_LT x y)
  trans (Right x) (Right y) = Right (trans {lt} x y)

  ||| `<=` is antisymmetric.
  export
  0 antisym :  Strict a lt eq
            => Either (lt m n) (eq m n)
            -> Either (lt n m) (eq m n)
            -> eq m n
  antisym (Right x) _         = x
  antisym (Left x)  (Right y) = y
  antisym (Left x)  (Left y)  = void (irrefl $ trans x y)

||| `k <= m` and `m == n` implies `k <= n`
export
0 trans_LTE_EQ :  Strict a lt eq
               => Either (lt k m) (eq k m)
               -> eq m n
               -> Either (lt k n) (eq k n)
trans_LTE_EQ lte eq = trans lte (Right eq)

||| `k == m` and `m <= n` implies `(k <= n)`
export
0 trans_EQ_LTE :  Strict a lt eq
               => eq k m
               -> Either (lt m n) (eq m n)
               -> Either (lt k n) (eq k n)
trans_EQ_LTE eq lte = trans (Right eq) lte

namespace GTE

  ||| `>=` is transitive.
  export
  0 trans :  Strict a lt eq
          => Either (lt m k) (eq m k)
          -> Either (lt n m) (eq n m)
          -> Either (lt n k) (eq n k)
  trans (Left x)  y         = Left (trans_GT_GTE x y)
  trans (Right x) (Left y)  = Left (trans_EQ_GT (sym {lt} x) y)
  trans (Right x) (Right y) = Right (trans {lt} y x)

  ||| `>=` is antisymmetric.
  export
  0 antisym :  Strict a lt eq
            => Either (lt n m) (eq m n)
            -> Either (lt m n) (eq m n)
            -> eq m n
  antisym (Right x) _         = x
  antisym (Left x)  (Right y) = y
  antisym (Left x)  (Left y)  = void (irrefl $ trans x y)

||| `k >= m` and `m == n` implies `k >= n`
export
0 trans_GTE_EQ :  Strict a lt eq
               => Either (lt m k) (eq m k)
               -> eq m n
               -> Either (lt n k) (eq n k)
trans_GTE_EQ gte eq = trans gte (Right $ sym {lt} eq)

||| `k == m` and `m <= n` implies `(k <= n)`
export
0 trans_EQ_GTE :  Strict a lt eq
               => eq k m
               -> Either (lt n m) (eq n m)
               -> Either (lt n k) (eq n k)
trans_EQ_GTE eq gte = trans (Right $ sym {lt} eq) gte

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

||| `m < n` implies `Not (m > n)`.
export
0 LT_not_GT : Strict a lt eq => lt m n -> Not (lt n m)
LT_not_GT isLT isGT = case trichotomy m n of
  LT _ _ g => g isGT
  EQ _ _ g => g isGT
  GT f _ _ => f isLT

||| `m < n` implies `Not (m == n)`.
export
0 LT_not_EQ : Strict a lt eq => lt m n -> Not (eq m n)
LT_not_EQ isLT isEQ = case trichotomy m n of
  LT _ g _ => g isEQ
  EQ f _ _ => f isLT
  GT _ g _ => g isEQ

||| `m < n` implies `Not (m >= n)`.
export
0 LT_not_GTE : Strict a lt eq => lt m n -> Not (Either (lt n m) (eq n m))
LT_not_GTE l = either (LT_not_GT l) (\e => LT_not_EQ l (sym {lt} e))

||| `Not (m < n)` implies `m >= n`.
export
0 Not_LT_to_GTE : Strict a lt eq => Not (lt m n) -> Either (lt n m) (eq n m)
Not_LT_to_GTE f = case trichotomy m n of
  LT x _ _ => void (f x)
  EQ _ x _ => Right (sym {lt} x)
  GT _ _ x => Left x

||| `m == n` implies `Not (m < n)`.
export
0 EQ_not_LT : Strict a lt eq => eq m n -> Not (lt m n)
EQ_not_LT = flip LT_not_EQ

||| `m == n` implies `Not (m > n)`.
export
0 EQ_not_GT : Strict a lt eq => eq m n -> Not (lt n m)
EQ_not_GT isEQ = EQ_not_LT (sym {lt} isEQ)

||| `m == n` implies `Not (m /= n)`.
export
0 EQ_not_NEQ : Strict a lt eq => eq m n -> Not (Either (lt m n) (lt n m))
EQ_not_NEQ isEQ = either (EQ_not_LT isEQ) (EQ_not_GT isEQ)

||| `Not (m < n)` implies `m >= n`.
export
0 Not_EQ_to_NEQ : Strict a lt eq => Not (eq m n) -> Either (lt m n) (lt n m)
Not_EQ_to_NEQ f = case trichotomy m n of
  LT x _ _ => Left x
  EQ _ x _ => void (f x)
  GT _ _ x => Right x

||| `m > n` implies `Not (m < n)`.
export
0 GT_not_LT : Strict a lt eq => lt n m -> Not (lt m n)
GT_not_LT = LT_not_GT

||| `m > n` implies `Not (m == n)`.
export
0 GT_not_EQ : Strict a lt eq => lt n m -> Not (eq m n)
GT_not_EQ = flip EQ_not_GT

||| `m > n` implies `Not (m <= n)`.
export
0 GT_not_LTE : Strict a lt eq => lt n m -> Not (Either (lt m n) (eq m n))
GT_not_LTE gt = either (GT_not_LT gt) (GT_not_EQ gt)

||| `Not (m > n)` implies `m <= n`.
export
0 Not_GT_to_LTE : Strict a lt eq => Not (lt n m) -> Either (lt m n) (eq m n)
Not_GT_to_LTE f = case trichotomy m n of
  LT x _ _ => Left x
  EQ _ x _ => Right x
  GT _ _ x => void (f x)

||| `m <= n` implies `Not (m > n)`.
export
0 LTE_not_GT : Strict a lt eq => (Either (lt m n) (eq m n)) -> Not (lt n m)
LTE_not_GT = either LT_not_GT EQ_not_GT

||| `Not (m <= n)` implies `m > n`.
export
0 Not_LTE_to_GT : Strict a lt eq => Not (Either (lt m n) (eq m n)) -> lt n m
Not_LTE_to_GT f = case trichotomy m n of
  LT x _ _ => void (f $ Left x)
  EQ _ x _ => void (f $ Right x)
  GT _ _ x => x

||| `m <= n` and `m >= n` implies `m == n`.
export
0 LTE_and_GTE_to_EQ :  Strict a lt eq
                    => Either (lt m n) (eq m n)
                    -> Either (lt n m) (eq n m)
                    -> eq m n
LTE_and_GTE_to_EQ (Left x)  (Right y) = sym {lt} y
LTE_and_GTE_to_EQ (Right x) _         = x
LTE_and_GTE_to_EQ (Left x)  (Left y)  = void (LT_not_GT x y)

||| `m <= n` and `m /= n` implies `m < n`.
export
0 LTE_and_NEQ_to_LT :  Strict a lt eq
                    => Either (lt m n) (eq m n)
                    -> Either (lt m n) (lt n m)
                    -> lt m n
LTE_and_NEQ_to_LT (Left x)  _         = x
LTE_and_NEQ_to_LT (Right _) (Left x)  = x
LTE_and_NEQ_to_LT (Right x) (Right y) = void (EQ_not_GT x y)

||| `m /= n` implies `Not (m == n)`.
export
0 NEQ_not_EQ : Strict a lt eq => Either (lt m n) (lt n m) -> Not (eq m n)
NEQ_not_EQ = either LT_not_EQ GT_not_EQ

||| `Not (m /= n)` implies `m == n`.
export
0 Not_NEQ_to_EQ : Strict a lt eq => Not (Either (lt m n) (lt n m)) -> eq m n
Not_NEQ_to_EQ f = case trichotomy m n of
  LT x _ _ => void (f $ Left x)
  EQ _ x _ => x
  GT _ _ x => void (f $ Right x)

||| `m /= n` and `m <= n` implies `m < n`.
export
0 NEQ_and_LTE_to_LT :  Strict a lt eq
                    => Either (lt m n) (lt n m)
                    -> Either (lt m n) (eq m n)
                    -> lt m n
NEQ_and_LTE_to_LT = flip LTE_and_NEQ_to_LT

||| `m /= n` and `m <= n` implies `m < n`.
export
0 NEQ_and_GTE_to_GT :  Strict a lt eq
                    => Either (lt m n) (lt n m)
                    -> Either (lt n m) (eq n m)
                    -> lt n m
NEQ_and_GTE_to_GT (Right x) _         = x
NEQ_and_GTE_to_GT (Left _)  (Left y)  = y
NEQ_and_GTE_to_GT (Left x)  (Right y) = void (GT_not_EQ x y)

||| `m >= n` implies `Not (m < n)`.
export
0 GTE_not_LT : Strict a lt eq => Either (lt n m) (eq n m) -> Not (lt m n)
GTE_not_LT = either GT_not_LT EQ_not_GT

||| `Not (m >= n)` implies `m < n`.
export
0 Not_GTE_to_LT : Strict a lt eq => Not (Either (lt n m) (eq n m)) -> lt m n
Not_GTE_to_LT f = case trichotomy m n of
  LT x _ _ => x
  EQ _ x _ => void (f $ Right (sym {lt} x))
  GT _ _ x => void (f $ Left x)

||| `m >= n` and `m <= n` implies `m == n`.
export
0 GTE_and_LTE_to_EQ :  Strict a lt eq
                    => Either (lt n m) (eq n m)
                    -> Either (lt m n) (eq m n)
                    -> eq m n
GTE_and_LTE_to_EQ = flip LTE_and_GTE_to_EQ

||| `m >= n` and `m /= n` implies `m > n`.
export
0 GTE_and_NEQ_to_GT :  Strict a lt eq
                    => Either (lt n m) (eq n m)
                    -> Either (lt m n) (lt n m)
                    -> lt n m
GTE_and_NEQ_to_GT = flip NEQ_and_GTE_to_GT
