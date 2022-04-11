module Algebra.Solver.Ring.Expr

import public Data.List.Elem
import public Algebra.Ring
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Natural Numbers
--------------------------------------------------------------------------------

public export
pow : Ring a => a -> Nat -> a
pow x 0     = 1
pow x (S k) = x * pow x k

--------------------------------------------------------------------------------
--          Expression
--------------------------------------------------------------------------------

public export
data Expr : (a : Type) -> (as : List a) -> Type where
  Lit   : (v : a) -> Expr a as
  Var   : (x : a) -> Elem x as -> Expr a as
  Neg   : Expr a as -> Expr a as
  Plus  : (x,y : Expr a as) -> Expr a as
  Mult  : (x,y : Expr a as) -> Expr a as
  Minus : (x,y : Expr a as) -> Expr a as

public export
Num a => Num (Expr a as) where
  (+) = Plus
  (*) = Mult
  fromInteger = Lit . fromInteger

public export
Neg a => Neg (Expr a as) where
  negate = Neg
  (-)    = Minus

public export
var : {0 as : List a} -> (x : a) -> Elem x as => Expr a as
var x = Var x %search

public export
v : {0 as : List a} -> (x : a) -> Elem x as => Expr a as
v = var

public export
eval : Ring a => Expr a as -> a
eval (Lit v)     = v
eval (Var x y)   = x
eval (Neg v)     = neg $ eval v
eval (Plus x y)  = eval x + eval y
eval (Mult x y)  = eval x * eval y
eval (Minus x y) = eval x - eval y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
0 ppow : Ring a
       => (m,n : Nat)
       -> (x   : a)
       -> pow x (m + n) === pow x m * pow x n
ppow 0     n x = sym multOneLeftNeutral
ppow (S k) n x = Calc $
  |~ x * pow x (plus k n)
  ~~ x * (pow x k * pow x n) ... cong (x*) (ppow k n x)
  ~~ (x * pow x k) * pow x n ... multAssociative
