module Data.Prim.Bits32

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
data (<) : (m,n : Bits32) -> Type where
  LT : {0 m,n : Bits32} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Bits32) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Bits32) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Bits32) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Bits32) -> Type
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
comp : (m,n : Bits32) -> Trichotomy (<) m n
comp m n = case prim__lt_Bits32 m n of
  0 => case prim__eq_Bits32 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Strict Bits32 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits32`
public export
MinBits32 : Bits32
MinBits32 = 0

||| Upper bound of `Bits32`
public export
MaxBits32 : Bits32
MaxBits32 = 0xffffffff

||| `m >= 0` for all `m` of type `Bits32`.
export
0 GTE_MinBits32 : (m : Bits32) -> m >= MinBits32
GTE_MinBits32 m = case comp MinBits32 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits32 smaller than 0"

||| Not value of type `Bits32` is less than zero.
export
0 Not_LT_MinBits32 : m < 0 -> Void
Not_LT_MinBits32 = GTE_not_LT (GTE_MinBits32 m)

||| `m <= MaxBits32` for all `m` of type `Bits32`.
export
0 LTE_MaxBits32 : (m : Bits32) -> m <= MaxBits32
LTE_MaxBits32 m = case comp m MaxBits32 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits32 greater than \{show MaxBits32}"

||| Not value of type `Bits32` is greater than `MaxBits32`.
export
0 Not_GT_MaxBits32 : m > MaxBits32 -> Void
Not_GT_MaxBits32 = LTE_not_GT (LTE_MaxBits32 m)

||| Every value of type `Bits32` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits32) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Bits32 (<) where
  wellFounded = accessLT

||| Every value of type `Bits32` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Bits32) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Bits32 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
|||
||| This uses `0 < d` as a constraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
export %inline
sdiv : (n,d : Bits32) -> (0 prf : 0 < d) => Bits32
sdiv n d = n `div` d

||| Refined division.
|||
||| This comes with a proof that the result is
||| strictly smaller than `n`.
|||
||| This uses `0 < n` as a constraint instead
||| of `0 /= n`, because in my experience, the former
||| is much more useful.
export %inline
rdiv :  (n,d : Bits32)
     -> (0 dgt1 : 1 < d)
     => (0 ngt0 : 0 < n)
     => Subset Bits32 (< n)
rdiv n d = Element (n `div` d) (LT unsafeRefl)

||| Safe modulo.
|||
||| This uses `0 < d` as a constraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
|||
||| If you need the postcondition that the result is strictly
||| smaller than `d`, use `rmod` instead.
export %inline
smod : (n,d : Bits32) -> (0 prf : 0 < d) => Bits32
smod n d = n `mod` d

||| Refined modulo.
|||
||| This comes with a proof that the result is strictly smaller
||| than `d`.
|||
||| It uses `0 < d` as a constraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
export %inline
rmod : (n,d : Bits32) -> (0 prf : 0 < d) => Subset Bits32 (< d)
rmod n d = Element (n `mod` d) (LT unsafeRefl)
