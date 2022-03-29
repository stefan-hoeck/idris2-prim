module Data.Prim.Int

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
data (<) : (m,n : Int) -> Type where
  LT : {0 m,n : Int} -> (0 prf : (m < n) === True) -> m < n

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
0 (>) : (m,n : Int) -> Type
m > n = n < m

||| `m <= n` mean that either `m < n` or `m === n` holds.
public export
0 (<=) : (m,n : Int) -> Type
m <= n = Either (m < n) (m === n)

||| Flipped version of `(<=)`.
public export
0 (>=) : (m,n : Int) -> Type
m >= n = n <= m

||| `m /= n` mean that either `m < n` or `m > n` holds.
public export
0 (/=) : (m,n : Int) -> Type
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
comp : (m,n : Int) -> Trichotomy (<) m n
comp m n = case prim__lt_Int m n of
  0 => case prim__eq_Int m n of
    0 => GT (ltNotGT $ LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (LT unsafeRefl)
    x => EQ (eqNotLT unsafeRefl) (unsafeRefl) (eqNotLT unsafeRefl)
  x => LT (LT unsafeRefl) (ltNotEQ $ LT unsafeRefl) (ltNotGT $ LT unsafeRefl)

export
Total Int (<) where
  trichotomy   = comp
  transLT p q  = strictLT p $ strictLT q $ LT unsafeRefl

--------------------------------------------------------------------------------
--          Ring Solver
--------------------------------------------------------------------------------

public export
record SSInt (as : List Int) (s : Sum Int as) where
  constructor SS
  sum   : Sum Int as
  0 prf : esum sum === esum s

public export
sumInt_ : (s : Sum Int as) -> SSInt as s
sumInt_ []           = SS [] Refl
sumInt_ (T f p :: y) =
  let SS sy py = sumInt_ y
   in case f of
        0 => SS sy (psum0 py)
        _ => SS (T f p :: sy) (cong ((f * eprod p) +) py)

public export
normInt : {as : List Int} -> Expr Int as -> Sum Int as
normInt e = sum $ sumInt_ $ normalize e

0 pnormInt :  {as : List Int}
          -> (e : Expr Int as)
          -> eval e === esum (normInt e)
pnormInt e with (sumInt_ $ normalize e)
  pnormInt e | SS sInt prf = Calc $
    |~ eval e
    ~~ esum (normalize e)  ...(pnormalize e)
    ~~ esum sInt            ..<(prf)

export
0 solve :  (as : List Int)
        -> (e1,e2 : Expr Int as)
        -> (prf : normInt e1 === normInt e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normInt e1) ...(pnormInt e1)
  ~~ esum (normInt e2) ...(cong esum prf)
  ~~ eval e2           ..<(pnormInt e2)

--------------------------------------------------------------------------------
--          Arithmetics
--------------------------------------------------------------------------------

||| Safe division.
export %inline
sdiv : (n,d : Int) -> (0 prf : d /= 0) => Int
sdiv n d = n `div` d

||| Safe modulo.
export %inline
smod : (n,d : Int) -> (0 prf : d /= 0) => Int
smod n d = n `mod` d
