module Data.Prim.Int64

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
data (<) : (m,n : Int64) -> Type where
  LT : {0 m,n : Int64} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Int64) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Int64) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Int64) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Int64) -> Type
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
comp : (m,n : Int64) -> Trichotomy (<) m n
comp m n = case prim__lt_Int64 m n of
  0 => case prim__eq_Int64 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Total Int64 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int64`
public export
MinInt64 : Int64
MinInt64 = -0x8000000000000000

||| Upper bound of `Int64`
public export
MaxInt64 : Int64
MaxInt64 = 0x7fffffffffffffff

||| `m >= MinInt64` for all `m` of type `Int64`.
export
0 GTE_MinInt64 : (m : Int64) -> m >= MinInt64
GTE_MinInt64 m = case comp MinInt64 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int64 smaller than \{show MinInt64}"

||| Not value of type `Int64` is less than zero.
export
0 Not_LT_MinInt64 : m < MinInt64 -> Void
Not_LT_MinInt64 = GTE_not_LT (GTE_MinInt64 m)

||| `m <= MaxInt64` for all `m` of type `Int64`.
export
0 LTE_MaxInt64 : (m : Int64) -> m <= MaxInt64
LTE_MaxInt64 m = case comp m MaxInt64 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int64 greater than \{show MaxInt64}"

||| Not value of type `Int64` is greater than `MaxInt64`.
export
0 Not_GT_MaxInt64 : m > MaxInt64 -> Void
Not_GT_MaxInt64 = LTE_not_GT (LTE_MaxInt64 m)

||| Every value of type `Int64` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int64) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Int64 (<) where
  wellFounded = accessLT

||| Every value of type `Int64` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Int64) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Int64 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Ring Solver
--------------------------------------------------------------------------------

public export
record SS64 (as : List Int64) (s : Sum Int64 as) where
  constructor SS
  sum   : Sum Int64 as
  0 prf : esum sum === esum s

public export
sum64_ : (s : Sum Int64 as) -> SS64 as s
sum64_ []           = SS [] Refl
sum64_ (T f p :: y) =
  let SS sy py = sum64_ y
   in case f of
        0 => SS sy (psum0 py)
        _ => SS (T f p :: sy) (cong ((f * eprod p) +) py)

public export
norm64 : {as : List Int64} -> Expr Int64 as -> Sum Int64 as
norm64 e = sum $ sum64_ $ normalize e

0 pnorm64 :  {as : List Int64}
          -> (e : Expr Int64 as)
          -> eval e === esum (norm64 e)
pnorm64 e with (sum64_ $ normalize e)
  pnorm64 e | SS s64 prf = Calc $
    |~ eval e
    ~~ esum (normalize e)  ...(pnormalize e)
    ~~ esum s64            ..<(prf)

export
0 solve :  (as : List Int64)
        -> (e1,e2 : Expr Int64 as)
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
export %inline
sdiv : (n,d : Int64) -> (0 prf : d /= 0) => Int64
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Int64) -> (0 prf : d /= 0) => Int64
smod n d = n `mod` d
