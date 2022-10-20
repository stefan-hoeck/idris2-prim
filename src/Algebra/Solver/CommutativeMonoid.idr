module Algebra.Solver.CommutativeMonoid

import public Algebra.CommutativeMonoid
import public Algebra.Solver.Prod
import Syntax.PreorderReasoning

%default total

public export
data Expr : (a : Type) -> (as : List a) -> Type where
  Lit     : (x : a) -> Expr a as
  Var     : (x : a) -> Elem x as -> Expr a as
  Neutral : Expr a as
  Append  : Expr a as -> Expr a as -> Expr a as

public export
FromString a => FromString (Expr a as) where
  fromString = Lit . fromString

public export
Semigroup (Expr a as) where
  (<+>) = Append

public export
Monoid (Expr a as) where
  neutral = Neutral

public export
normalize : Monoid a => {as : List a} -> Expr a as -> Term a as
normalize (Lit x)      = T x one
normalize (Var x y)    = T neutral (fromVar y)
normalize Neutral      = T neutral one
normalize (Append x y) = append (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

public export
eval : Monoid a => Expr a as -> a
eval (Lit x)      = x
eval (Var x y)    = x
eval Neutral      = neutral
eval (Append x y) = eval x <+> eval y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 pnorm :
     {mon : _}
  -> CommutativeMonoid a mon
  => (e : Expr a as)
  -> eval e === emterm (normalize e)
pnorm (Lit x) = Calc $
  |~ x
  ~~ x <+> neutral         ..< appendRightNeutral
  ~~ x <+> emprod {as} one ..< cong (x <+>) (pone as)

pnorm (Var x y) = Calc $
 |~ x
 ~~ emprod (fromVar y)             ..< pvar as y
 ~~ neutral <+> emprod (fromVar y) ..< cm_appendLeftNeutral

pnorm Neutral = Calc $
  |~ neutral
  ~~ neutral <+> neutral         ..< appendRightNeutral
  ~~ neutral <+> emprod {as} one ..< cong (neutral <+>) (pone as)

pnorm (Append x y) = Calc $
  |~ eval x <+> eval y
  ~~ emterm (normalize x) <+> eval y
     ... cong (<+> eval y) (pnorm x)
  ~~ emterm (normalize x) <+> emterm (normalize y)
     ... cong (emterm (normalize x) <+>) (pnorm y)
  ~~ emterm (append (normalize x) (normalize y))
     ... pappend (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :
     {mon : _}
  -> CommutativeMonoid a mon
  => (as : List a)
  -> (e1,e2 : Expr a as)
  -> (prf : normalize e1 === normalize e2)
  => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ emterm (normalize e1) ... pnorm e1
  ~~ emterm (normalize e2) ... cong emterm prf
  ~~ eval e2               ..< pnorm e2
