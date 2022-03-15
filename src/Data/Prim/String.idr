module Data.Prim.String

import public Data.DPair
import public Data.Prim.Ord

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

--------------------------------------------------------------------------------
--          (<)
--------------------------------------------------------------------------------

||| Witness that `m < n === True`.
export
data (<) : (m,n : String) -> Type where
  LT : {0 m,n : String} -> (0 prf : (m < n) === True) -> m < n

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
--          (==)
--------------------------------------------------------------------------------

||| Witness that `m == n === True`.
export
data (==) : (m,n : String) -> Type where
  EQ : {0 m,n : String} -> (0 prf : (m == n) === True) -> m == n

||| Contructor for `(==)`.
|||
||| This can only be used in an erased context.
export %hint
0 mkEQ : (0 prf : (m == n) === True) -> m == n
mkEQ = EQ

||| Extractor for `(==)`.
|||
||| This can only be used in an erased context.
export
0 runEQ : m == n -> (m == n) === True
runEQ (EQ prf) = prf

||| We don't trust values of type `(==)` too much,
||| so we use this when creating magical results.
export
strictEQ : (0 p : m == n) -> Lazy c -> c
strictEQ (EQ prf) x = x

--------------------------------------------------------------------------------
--          Aliases
--------------------------------------------------------------------------------

||| Flipped version of `(<)`.
public export
0 (>) : (m,n : String) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m == n` holds.
public export
0 (<=) : (m,n : String) -> Type
m <= n = Either (m < n) (m == n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : String) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : String) -> Type
m /= n = Either (m < n) (m > n)

--------------------------------------------------------------------------------
--          Order
--------------------------------------------------------------------------------

0 eqNotLT : m == n -> Not (m < n)
eqNotLT x = strictEQ x $ assert_total (idris_crash "IMPOSSIBLE: EQ and LT")

0 eqNotGT : m == n -> Not (n < m)
eqNotGT x = strictEQ x $ assert_total (idris_crash "IMPOSSIBLE: EQ and GT")

0 ltNotEQ : m < n -> Not (m == n)
ltNotEQ x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and EQ")

0 ltNotGT : m < n -> Not (n < m)
ltNotGT x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and GT")

export
comp : (m,n : String) -> Trichotomy (<) (==) m n
comp m n = case prim__lt_String m n of
  0 => case prim__eq_String m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT $ EQ unsafeRefl) (EQ unsafeRefl) (eqNotGT $ EQ unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
PrimOrd String (<) (==) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl
  reflEQ       = EQ unsafeRefl
  elim _ eq pm = strictEQ eq $ believe_me pm

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `String`
public export
MinString : String
MinString = ""

||| `m >= MinString` for all `m` of type `String`.
export
0 GTE_MinString : (m : String) -> m >= MinString
GTE_MinString m = case comp MinString m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: String smaller than 0"

||| Not value of type `String` is less than `MinString`.
export
0 Not_LT_MinString : m < MinString -> Void
Not_LT_MinString = GTE_not_LT (GTE_MinString m)
