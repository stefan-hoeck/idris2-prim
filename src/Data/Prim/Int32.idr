module Data.Prim.Int32

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
data (<) : (m,n : Int32) -> Type where
  LT : {0 m,n : Int32} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Int32) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Int32) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Int32) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Int32) -> Type
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
comp : (m,n : Int32) -> Trichotomy (<) m n
comp m n = case prim__lt_Int32 m n of
  0 => case prim__eq_Int32 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Strict Int32 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int32`
public export
MinInt32 : Int32
MinInt32 = -0x80000000

||| Upper bound of `Int32`
public export
MaxInt32 : Int32
MaxInt32 = 0x7fffffff

||| `m >= MinInt32` for all `m` of type `Int32`.
export
0 GTE_MinInt32 : (m : Int32) -> m >= MinInt32
GTE_MinInt32 m = case comp MinInt32 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int32 smaller than \{show MinInt32}"

||| Not value of type `Int32` is less than zero.
export
0 Not_LT_MinInt32 : m < MinInt32 -> Void
Not_LT_MinInt32 = GTE_not_LT (GTE_MinInt32 m)

||| `m <= MaxInt32` for all `m` of type `Int32`.
export
0 LTE_MaxInt32 : (m : Int32) -> m <= MaxInt32
LTE_MaxInt32 m = case comp m MaxInt32 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int32 greater than \{show MaxInt32}"

||| Not value of type `Int32` is greater than `MaxInt32`.
export
0 Not_GT_MaxInt32 : m > MaxInt32 -> Void
Not_GT_MaxInt32 = LTE_not_GT (LTE_MaxInt32 m)

||| Every value of type `Int32` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int32) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Int32 (<) where
  wellFounded = accessLT

||| Every value of type `Int32` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Int32) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Int32 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
export %inline
sdiv : (n,d : Int32) -> (0 prf : d /= 0) => Int32
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Int32) -> (0 prf : d /= 0) => Int32
smod n d = n `mod` d
