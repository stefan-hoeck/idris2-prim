module Algebra.Solver.Monoid

import Algebra.Monoid
import Syntax.PreorderReasoning

%default total

public export
data Expr : (a : Type) -> Type where
  Var     : (x : a) -> Expr a
  Neutral : Expr a
  Append  : Expr a -> Expr a -> Expr a

public export
Semigroup (Expr a) where
  (<+>) = Append

public export
Monoid (Expr a) where
  neutral = Neutral

public export
eval : LMonoid a => Expr a -> a
eval (Var x)      = x
eval Neutral      = neutral
eval (Append x y) = eval x <+> eval y

--------------------------------------------------------------------------------
--          Sum
--------------------------------------------------------------------------------

public export
esum : LMonoid a => List a -> a
esum []       = neutral
esum (h :: t) = h <+> esum t

public export
normalize : Expr a -> List a
normalize (Var x)      = x :: []
normalize Neutral      = []
normalize (Append x y) = normalize x ++ normalize y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 psum :
     {auto _ : LMonoid a}
  -> (xs,ys : List a)
  -> esum (xs ++ ys) === esum xs <+> esum ys
psum []        ys = sym appendLeftNeutral
psum (x :: xs) ys = Calc $
  |~ x <+> esum (xs ++ ys)
  ~~ x <+> (esum xs <+> esum ys) ... cong (x <+>) (psum xs ys)
  ~~ (x <+> esum xs) <+> esum ys ... appendAssociative


0 pnorm : LMonoid a => (e : Expr a) -> eval e === esum (normalize e)
pnorm (Var x)      = sym appendRightNeutral
pnorm Neutral      = Refl
pnorm (Append x y) = Calc $
  |~ eval x <+> eval y
  ~~ esum (normalize x) <+> eval y
     ... cong (<+> eval y) (pnorm x)
  ~~ esum (normalize x) <+> esum (normalize y)
     ... cong (esum (normalize x) <+>) (pnorm y)
  ~~ esum (normalize x ++ normalize y)
     ..< psum (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     {auto _ : LMonoid a}
  -> (e1,e2 : Expr a)
  -> {auto prf : normalize e1 === normalize e2}
  -> eval e1 === eval e2
solve e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normalize e1) ... pnorm e1
  ~~ esum (normalize e2) ... cong esum prf
  ~~ eval e2             ..< pnorm e2

--------------------------------------------------------------------------------
--          Example
--------------------------------------------------------------------------------

0 solverExample : {x,y,z : String}
                -> x ++ ((y ++ "") ++ z) === ("" ++ x) ++ (y ++ z)
solverExample =
  solve
    (Var x <+> ((Var y <+> Neutral) <+> Var z))
    ((Neutral <+> Var x) <+> (Var y <+> Var z))
