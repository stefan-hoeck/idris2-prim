module Data.Prim.Integer

import public Control.WellFounded
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
--          (==)
--------------------------------------------------------------------------------

||| Witness that `m == n === True`.
export
data (==) : (m,n : Integer) -> Type where
  EQ : {0 m,n : Integer} -> (0 prf : (m == n) === True) -> m == n

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
0 (>) : (m,n : Integer) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m == n` holds.
public export
0 (<=) : (m,n : Integer) -> Type
m <= n = Either (m < n) (m == n)

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

0 eqNotLT : m == n -> Not (m < n)
eqNotLT x = strictEQ x $ assert_total (idris_crash "IMPOSSIBLE: EQ and LT")

0 eqNotGT : m == n -> Not (n < m)
eqNotGT x = strictEQ x $ assert_total (idris_crash "IMPOSSIBLE: EQ and GT")

0 ltNotEQ : m < n -> Not (m == n)
ltNotEQ x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and EQ")

0 ltNotGT : m < n -> Not (n < m)
ltNotGT x = strictLT x $ assert_total (idris_crash "IMPOSSIBLE: LT and GT")

export
comp : (m,n : Integer) -> Trichotomy (<) (==) m n
comp m n = case prim__lt_Integer m n of
  0 => case prim__eq_Integer m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT $ EQ unsafeRefl) (EQ unsafeRefl) (eqNotGT $ EQ unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Strict Integer (<) (==) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl
  reflEQ       = EQ unsafeRefl
  elim _ eq pm = strictEQ eq $ believe_me pm

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
export %inline
sdiv : (n,d : Integer) -> (0 prf : d /= 0) => Integer
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Integer) -> (0 prf : d /= 0) => Integer
smod n d = n `mod` d
