module Algebra.Solver.Semigroup

import Algebra.Semigroup
import Data.List1
import Syntax.PreorderReasoning

%default total

public export
data Expr : (a : Type) -> Type where
  Var    : (x : a) -> Expr a
  Append : Expr a -> Expr a -> Expr a

public export
Semigroup (Expr a) where
  (<+>) = Append

public export
eval : LSemigroup a => Expr a -> a
eval (Var x)    = x
eval (Append x y) = eval x <+> eval y

--------------------------------------------------------------------------------
--          Sum
--------------------------------------------------------------------------------

public export
esum' : LSemigroup a => a -> List a -> a
esum' v []       = v
esum' v (h :: t) = v <+> esum' h t

public export
esum : LSemigroup a => List1 a -> a
esum (v ::: vs) = esum' v vs

public export
normalize : Expr a -> List1 a
normalize (Var x)      = x ::: []
normalize (Append x y) = normalize x ++ normalize y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 psum' :  LSemigroup a
        => (x,y   : a)
        -> (xs,ys : List a)
        -> esum' x (xs ++ (y :: ys)) === esum' x xs <+> esum' y ys
psum' x y []        ys = Refl
psum' x y (v :: vs) ys = Calc $
  |~ x <+> esum' v (vs ++ (y :: ys))
  ~~ x <+> (esum' v vs <+> esum' y ys) ... cong (x <+>) (psum' v y vs ys)
  ~~ (x <+> esum' v vs) <+> esum' y ys ... appendAssociative

0 psum :  LSemigroup a
       => (xs,ys : List1 a)
       -> esum (xs ++ ys) === esum xs <+> esum ys
psum (x ::: xs) (y ::: ys) = psum' x y xs ys

0 pnorm : LSemigroup a => (e : Expr a) -> eval e === esum (normalize e)
pnorm (Var x)      = Refl
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
0 solve :  LSemigroup a
        => (e1,e2 : Expr a)
        -> (prf : normalize e1 === normalize e2)
        => eval e1 === eval e2
solve e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normalize e1) ... pnorm e1
  ~~ esum (normalize e2) ... cong esum prf
  ~~ eval e2             ..< pnorm e2
