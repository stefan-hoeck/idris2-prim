module Data.Prim.Int8

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
data (<) : (m,n : Int8) -> Type where
  LT : {0 m,n : Int8} -> (0 prf : (m < n) === True) -> m < n

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
data (==) : (m,n : Int8) -> Type where
  EQ : {0 m,n : Int8} -> (0 prf : (m == n) === True) -> m == n

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
0 (>) : (m,n : Int8) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m == n` holds.
public export
0 (<=) : (m,n : Int8) -> Type
m <= n = Either (m < n) (m == n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Int8) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Int8) -> Type
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
comp : (m,n : Int8) -> Trichotomy (<) (==) m n
comp m n = case prim__lt_Int8 m n of
  0 => case prim__eq_Int8 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT $ EQ unsafeRefl) (EQ unsafeRefl) (eqNotGT $ EQ unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
PrimOrd Int8 (<) (==) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl
  reflEQ       = EQ unsafeRefl
  elim _ eq pm = strictEQ eq $ believe_me pm

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int8`
public export
MinInt8 : Int8
MinInt8 = -0x80

||| Upper bound of `Int8`
public export
MaxInt8 : Int8
MaxInt8 = 0x7f

||| `m >= MinInt8` for all `m` of type `Int8`.
export
0 GTE_MinInt8 : (m : Int8) -> m >= MinInt8
GTE_MinInt8 m = case comp MinInt8 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int8 smaller than \{show MinInt8}"

||| Not value of type `Int8` is less than zero.
export
0 Not_LT_MinInt8 : m < MinInt8 -> Void
Not_LT_MinInt8 = GTE_not_LT (GTE_MinInt8 m)

||| `m <= MaxInt8` for all `m` of type `Int8`.
export
0 LTE_MaxInt8 : (m : Int8) -> m <= MaxInt8
LTE_MaxInt8 m = case comp m MaxInt8 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int8 greater than \{show MaxInt8}"

||| Not value of type `Int8` is greater than `MaxInt8`.
export
0 Not_GT_MaxInt8 : m > MaxInt8 -> Void
Not_GT_MaxInt8 = LTE_not_GT (LTE_MaxInt8 m)

||| Every value of type `Int8` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int8) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Int8 (<) where
  wellFounded = accessLT

||| Every value of type `Int8` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Int8) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Int8 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
export %inline
sdiv : (n,d : Int8) -> (0 prf : d /= 0) => Int8
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Int8) -> (0 prf : d /= 0) => Int8
smod n d = n `mod` d
