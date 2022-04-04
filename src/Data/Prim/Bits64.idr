module Data.Prim.Bits64

import public Control.WellFounded
import public Data.DPair
import public Data.Prim.Ord
import public Algebra.Solver.Ring
import Syntax.PreorderReasoning

%default total

unsafeRefl : a === b
unsafeRefl = believe_me (Refl {x = a})

--------------------------------------------------------------------------------
--          (<)
--------------------------------------------------------------------------------

||| Witness that `m < n === True`.
export
data (<) : (m,n : Bits64) -> Type where
  LT : {0 m,n : Bits64} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Bits64) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Bits64) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Bits64) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Bits64) -> Type
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
comp : (m,n : Bits64) -> Trichotomy (<) m n
comp m n = case prim__lt_Bits64 m n of
  0 => case prim__eq_Bits64 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Total Bits64 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Bits64`
public export
MinBits64 : Bits64
MinBits64 = 0

||| Upper bound of `Bits64`
public export
MaxBits64 : Bits64
MaxBits64 = 0xffffffffffffffff

||| `m >= 0` for all `m` of type `Bits64`.
export
0 GTE_MinBits64 : (m : Bits64) -> m >= MinBits64
GTE_MinBits64 m = case comp MinBits64 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total $ idris_crash "IMPOSSIBLE: Bits64 smaller than 0"

||| Not value of type `Bits64` is less than zero.
export
0 Not_LT_MinBits64 : m < 0 -> Void
Not_LT_MinBits64 = GTE_not_LT (GTE_MinBits64 m)

||| `m <= MaxBits64` for all `m` of type `Bits64`.
export
0 LTE_MaxBits64 : (m : Bits64) -> m <= MaxBits64
LTE_MaxBits64 m = case comp m MaxBits64 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Bits64 greater than \{show MaxBits64}"

||| Not value of type `Bits64` is greater than `MaxBits64`.
export
0 Not_GT_MaxBits64 : m > MaxBits64 -> Void
Not_GT_MaxBits64 = LTE_not_GT (LTE_MaxBits64 m)

||| Every value of type `Bits64` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Bits64) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Bits64 (<) where
  wellFounded = accessLT

||| Every value of type `Bits64` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Bits64) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Bits64 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Ring Solver
--------------------------------------------------------------------------------

public export
record SS64 (as : List Bits64) (s : Sum Bits64 as) where
  constructor SS
  sum   : Sum Bits64 as
  0 prf : esum sum === esum s

public export
sum64_ : (s : Sum Bits64 as) -> SS64 as s
sum64_ []           = SS [] Refl
sum64_ (T f p :: y) =
  let SS sy py = sum64_ y
   in case f of
        0 => SS sy (psum0 py)
        _ => SS (T f p :: sy) (cong ((f * eprod p) +) py)

public export
norm64 : {as : List Bits64} -> Expr Bits64 as -> Sum Bits64 as
norm64 e = sum $ sum64_ $ normalize e

0 pnorm64 :  {as : List Bits64}
          -> (e : Expr Bits64 as)
          -> eval e === esum (norm64 e)
pnorm64 e with (sum64_ $ normalize e)
  pnorm64 e | SS s64 prf = Calc $
    |~ eval e
    ~~ esum (normalize e)  ...(pnormalize e)
    ~~ esum s64            ..<(prf)

export
0 solve :  (as : List Bits64)
        -> (e1,e2 : Expr Bits64 as)
        -> (prf : norm64 e1 === norm64 e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (norm64 e1) ...(pnorm64 e1)
  ~~ esum (norm64 e2) ...(cong esum prf)
  ~~ eval e2          ..<(pnorm64 e2)

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
|||
||| This uses `0 < d` as a constraint instead
||| of `0 /= d`, because in my experience, the former
||| is much more useful.
export %inline
sdiv : (n,d : Bits64) -> (0 prf : 0 < d) => Bits64
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
rdiv :  (n,d : Bits64)
     -> (0 dgt1 : 1 < d)
     => (0 ngt0 : 0 < n)
     => Subset Bits64 (< n)
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
smod : (n,d : Bits64) -> (0 prf : 0 < d) => Bits64
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
rmod : (n,d : Bits64) -> (0 prf : 0 < d) => Subset Bits64 (< d)
rmod n d = Element (n `mod` d) (LT unsafeRefl)
