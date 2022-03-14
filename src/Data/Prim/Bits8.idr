module Data.Prim.Bits8

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
data (<) : (m,n : Bits8) -> Type where
  LT : {0 m,n : Bits8} -> (0 prf : (m < n) === True) -> m < n

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
data (==) : (m,n : Bits8) -> Type where
  EQ : {0 m,n : Bits8} -> (0 prf : (m == n) === True) -> m == n

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
0 (>) : (m,n : Bits8) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m == n` holds.
public export
0 (<=) : (m,n : Bits8) -> Type
m <= n = Either (m < n) (m == n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Bits8) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Bits8) -> Type
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
comp : (m,n : Bits8) -> Trichotomy (<) (==) m n
comp m n = case prim__lt_Bits8 m n of
  0 => case prim__eq_Bits8 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT $ EQ unsafeRefl) (EQ unsafeRefl) (eqNotGT $ EQ unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
PrimOrd Bits8 (<) (==) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl
  reflEQ       = EQ unsafeRefl
  elim _ eq pm = strictEQ eq $ believe_me pm

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits8`
public export
MinBits8 : Bits8
MinBits8 = 0

||| Upper bound of `Bits8`
public export
MaxBits8 : Bits8
MaxBits8 = 0xff

||| `m >= 0` for all `m` of type `Bits8`.
export
0 GTE_MinBits8 : (m : Bits8) -> m >= MinBits8
GTE_MinBits8 m = case comp MinBits8 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits8 smaller than 0"

||| Not value of type `Bits8` is less than zero.
export
0 Not_LT_MinBits8 : m < 0 -> Void
Not_LT_MinBits8 = GTE_not_LT (GTE_MinBits8 m)

||| `m <= MaxBits8` for all `m` of type `Bits8`.
export
0 LTE_MaxBits8 : (m : Bits8) -> m <= MaxBits8
LTE_MaxBits8 m = case comp m MaxBits8 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits8 greater than \{show MaxBits8}"

||| Not value of type `Bits8` is greater than `MaxBits8`.
export
0 Not_GT_MaxBits8 : m > MaxBits8 -> Void
Not_GT_MaxBits8 = LTE_not_GT (LTE_MaxBits8 m)

||| Every value of type `Bits8` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits8) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Bits8 (<) where
  wellFounded = accessLT

||| Every value of type `Bits8` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Bits8) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Bits8 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
|||
||| This uses `0 < d` as a contraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
export %inline
sdiv : (n,d : Bits8) -> (0 prf : 0 < d) => Bits8
sdiv n d = n `div` d

||| Refined division.
|||
||| This comes with a proof that the result is
||| strictly smaller than `n`.
|||
||| This uses `0 < n` as a contraint instead
||| of `0 /= n`, because in my experience, the former
||| is much more useful.
export %inline
rdiv :  (n,d : Bits8)
     -> (0 dgt1 : 1 < d)
     => (0 ngt0 : 0 < n)
     => Subset Bits8 (< n)
rdiv n d = Element (n `div` d) (LT unsafeRefl)

||| Safe modulo.
|||
||| This uses `0 < d` as a contraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
|||
||| If you need the postcondition that the result is strictly
||| smaller than `d`, use `rmod` instead.
export %inline
smod : (n,d : Bits8) -> (0 prf : 0 < d) => Bits8
smod n d = n `mod` d

||| Refined modulo.
|||
||| This comes with a proof that the result is strictly smaller
||| than `d`.
|||
||| It uses `0 < d` as a contraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
export %inline
rmod : (n,d : Bits8) -> (0 prf : 0 < d) => Subset Bits8 (< d)
rmod n d = Element (n `mod` d) (LT unsafeRefl)
