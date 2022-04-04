module Data.Prim.Int16

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
data (<) : (m,n : Int16) -> Type where
  LT : {0 m,n : Int16} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Int16) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Int16) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Int16) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Int16) -> Type
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
comp : (m,n : Int16) -> Trichotomy (<) m n
comp m n = case prim__lt_Int16 m n of
  0 => case prim__eq_Int16 m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Total Int16 (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Bounds and Well-Foundedness
--------------------------------------------------------------------------------

||| Lower bound of `Int16`
public export
MinInt16 : Int16
MinInt16 = -0x8000

||| Upper bound of `Int16`
public export
MaxInt16 : Int16
MaxInt16 = 0x7fff

||| `m >= MinInt16` for all `m` of type `Int16`.
export
0 GTE_MinInt16 : (m : Int16) -> m >= MinInt16
GTE_MinInt16 m = case comp MinInt16 m of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int16 smaller than \{show MinInt16}"

||| Not value of type `Int16` is less than zero.
export
0 Not_LT_MinInt16 : m < MinInt16 -> Void
Not_LT_MinInt16 = GTE_not_LT (GTE_MinInt16 m)

||| `m <= MaxInt16` for all `m` of type `Int16`.
export
0 LTE_MaxInt16 : (m : Int16) -> m <= MaxInt16
LTE_MaxInt16 m = case comp m MaxInt16 of
  LT x f g => %search
  EQ f x g => %search
  GT f g x => assert_total
            $ idris_crash "IMPOSSIBLE: Int16 greater than \{show MaxInt16}"

||| Not value of type `Int16` is greater than `MaxInt16`.
export
0 Not_GT_MaxInt16 : m > MaxInt16 -> Void
Not_GT_MaxInt16 = LTE_not_GT (LTE_MaxInt16 m)

||| Every value of type `Int16` is accessible with relation
||| to `(<)`.
export
accessLT : (m : Int16) -> Accessible (<) m
accessLT m = Access $ \n,lt => accessLT (assert_smaller m n)

||| `(<)` is well founded.
export %inline
WellFounded Int16 (<) where
  wellFounded = accessLT

||| Every value of type `Int16` is accessible with relation
||| to `(>)`.
export
accessGT : (m : Int16) -> Accessible (>) m
accessGT m = Access $ \n,gt => accessGT (assert_smaller m n)

||| `(>)` is well founded.
export %inline
[GT] WellFounded Int16 (>) where
  wellFounded = accessGT

--------------------------------------------------------------------------------
--          Ring Solver
--------------------------------------------------------------------------------

public export
record SS16 (as : List Int16) (s : Sum Int16 as) where
  constructor SS
  sum   : Sum Int16 as
  0 prf : esum sum === esum s

public export
sum16_ : (s : Sum Int16 as) -> SS16 as s
sum16_ []           = SS [] Refl
sum16_ (T f p :: y) =
  let SS sy py = sum16_ y
   in case f of
        0 => SS sy (psum0 py)
        _ => SS (T f p :: sy) (cong ((f * eprod p) +) py)

public export
norm16 : {as : List Int16} -> Expr Int16 as -> Sum Int16 as
norm16 e = sum $ sum16_ $ normalize e

0 pnorm16 :  {as : List Int16}
          -> (e : Expr Int16 as)
          -> eval e === esum (norm16 e)
pnorm16 e with (sum16_ $ normalize e)
  pnorm16 e | SS s16 prf = Calc $
    |~ eval e
    ~~ esum (normalize e)  ...(pnormalize e)
    ~~ esum s16            ..<(prf)

export
0 solve :  (as : List Int16)
        -> (e1,e2 : Expr Int16 as)
        -> (prf : norm16 e1 === norm16 e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (norm16 e1) ...(pnorm16 e1)
  ~~ esum (norm16 e2) ...(cong esum prf)
  ~~ eval e2          ..<(pnorm16 e2)

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
export %inline
sdiv : (n,d : Int16) -> (0 prf : d /= 0) => Int16
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Int16) -> (0 prf : d /= 0) => Int16
smod n d = n `mod` d
