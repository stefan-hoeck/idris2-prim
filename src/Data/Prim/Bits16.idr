module Data.Prim.Bits16

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
data (<) : (m,n : Bits16) -> Type where
  LT : {0 m,n : Bits16} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Bits16) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Bits16) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Bits16) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Bits16) -> Type
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
comp : (m,n : Bits16) -> Trichotomy (<) m n
comp m n = case prim__lt_Bits16 m n of
  0 => case prim__eq_Bits16 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Total Bits16 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits16`
public export
MinBits16 : Bits16
MinBits16 = 0

||| Upper bound of `Bits16`
public export
MaxBits16 : Bits16
MaxBits16 = 0xffff

||| `m >= 0` for all `m` of type `Bits16`.
export
0 GTE_MinBits16 : (m : Bits16) -> m >= MinBits16
GTE_MinBits16 m = case comp MinBits16 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits16 smaller than 0"

||| Not value of type `Bits16` is less than zero.
export
0 Not_LT_MinBits16 : m < 0 -> Void
Not_LT_MinBits16 = GTE_not_LT (GTE_MinBits16 m)

||| `m <= MaxBits16` for all `m` of type `Bits16`.
export
0 LTE_MaxBits16 : (m : Bits16) -> m <= MaxBits16
LTE_MaxBits16 m = case comp m MaxBits16 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits16 greater than \{show MaxBits16}"

||| Not value of type `Bits16` is greater than `MaxBits16`
export
0 Not_GT_MaxBits16 : m > MaxBits16 -> Void
Not_GT_MaxBits16 = LTE_not_GT (LTE_MaxBits16 m)

||| Every value of type `Bits16` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits16) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Bits16 (<) where
  wellFounded = accessLT

||| Every value of type `Bits16` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Bits16) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Bits16 (>) where
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
sdiv : (n,d : Bits16) -> (0 prf : 0 < d) => Bits16
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
rdiv :  (n,d : Bits16)
     -> (0 dgt1 : 1 < d)
     => (0 ngt0 : 0 < n)
     => Subset Bits16 (< n)
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
smod : (n,d : Bits16) -> (0 prf : 0 < d) => Bits16
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
rmod : (n,d : Bits16) -> (0 prf : 0 < d) => Subset Bits16 (< d)
rmod n d = Element (n `mod` d) (LT unsafeRefl)
