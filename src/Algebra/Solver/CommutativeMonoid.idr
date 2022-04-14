module Algebra.Solver.CommutativeMonoid

import public Algebra.Monoid
import public Algebra.Solver.Prod
import Syntax.PreorderReasoning

%default total

public export
times : CommutativeMonoid a => Nat -> a -> a
times 0     x = neutral
times (S k) x = x <+> times k x

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

--------------------------------------------------------------------------------
--          Normalization
--------------------------------------------------------------------------------

public export
record Term (a : Type) (as : List a) where
  constructor T
  factor : a
  prod   : Prod a as

public export
append : CommutativeMonoid a => Term a as -> Term a as -> Term a as
append (T f1 p1) (T f2 p2) = T (f1 <+> f2) (mult p1 p2)

public export
normalize : CommutativeMonoid a => {as : List a} -> Expr a as -> Term a as
normalize (Lit x)      = T x one
normalize (Var x y)    = T neutral (fromVar y)
normalize Neutral      = T neutral one
normalize (Append x y) = append (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

public export
eval : CommutativeMonoid a => Expr a as -> a
eval (Lit x)      = x
eval (Var x y)    = x
eval Neutral      = neutral
eval (Append x y) = eval x <+> eval y

public export
eprod : CommutativeMonoid a => {as : List a} -> Prod a as -> a
eprod []                        = neutral
eprod {as = v :: vs} (exp :: x) = times exp v <+> eprod x

public export
eterm : CommutativeMonoid a => {as : List a} -> Term a as -> a
eterm (T f p) = f <+> eprod p

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

0 p1324 :  CommutativeMonoid a
        => {k,l,m,n : a}
        -> (k <+> l) <+> (m <+> n) === (k <+> m) <+> (l <+> n)
p1324 = Calc $
  |~ (k <+> l) <+> (m <+> n)
  ~~ ((k <+> l) <+> m) <+> n ... appendAssociative
  ~~ (k <+> (l <+> m)) <+> n ..< cong (<+>n) appendAssociative
  ~~ (k <+> (m <+> l)) <+> n ... cong (\x => (k <+> x) <+> n) appendCommutative
  ~~ ((k <+> m) <+> l) <+> n ... cong (<+>n) appendAssociative
  ~~ (k <+> m) <+> (l <+> n) ..< appendAssociative

0 pone :  CommutativeMonoid a
       => (as : List a)
       -> eprod {as} Prod.one === Prelude.neutral
pone []        = Refl
pone (v :: vs) = Calc $
  |~ neutral <+> eprod {as = vs} one
  ~~ neutral <+> neutral             ... cong (neutral <+>) (pone vs)
  ~~ neutral                         ... appendLeftNeutral

export
0 pvar :  CommutativeMonoid a
       => (as : List a)
       -> (e  : Elem x as)
       -> eprod (fromVar {as} e) === x
pvar (x :: vs) Here      = Calc $
  |~ (x <+> neutral) <+> eprod {as = vs} one
  ~~ (x <+> neutral) <+> neutral ... cong ((x <+> neutral) <+>) (pone vs)
  ~~ x <+> neutral               ... appendRightNeutral
  ~~ x                           ... appendRightNeutral

pvar (v :: vs) (There y) = Calc $
  |~ neutral <+> eprod (fromVar y)
  ~~ eprod (fromVar y)             ... appendLeftNeutral
  ~~ x                             ... pvar vs y

pvar [] Here impossible
pvar [] (There y) impossible

0 ptimes :  CommutativeMonoid a
         => (m,n : Nat)
         -> (x : a)
         -> times m x <+> times n x === times (m + n) x
ptimes 0     n x = appendLeftNeutral
ptimes (S k) n x = Calc $
  |~ (x <+> times k x) <+> times n x
  ~~ x <+> (times k x <+> times n x) ..< appendAssociative
  ~~ x <+> times (k + n) x           ... cong (x <+>) (ptimes k n x)


0 ppm :  CommutativeMonoid a
      => (e1,e2 : Prod a as)
      -> eprod e1 <+> eprod e2 === eprod (mult e1 e2)
ppm []        []        = appendRightNeutral
ppm {as = v :: vs} (m :: xs) (n :: ys) = Calc $
  |~ (times m v <+> eprod xs) <+> (times n v <+> eprod ys)
  ~~ (times m v <+> times n v) <+> (eprod xs <+> eprod ys)
     ... p1324
  ~~ (times m v <+> times n v) <+> eprod (mult xs ys)
     ... cong ((times m v <+> times n v) <+>) (ppm xs ys)
  ~~ times (m + n) v <+> eprod (mult xs ys)
     ... cong (<+> eprod (mult xs ys)) (ptimes m n v)


0 pappend :  CommutativeMonoid a
          => (e1,e2 : Term a as)
          -> eterm e1 <+> eterm e2 === eterm (append e1 e2)
pappend (T f p) (T g q) = Calc $
  |~ (f <+> eprod p) <+> (g <+> eprod q)
  ~~ (f <+> g) <+> (eprod p <+> eprod q) ... p1324
  ~~ (f <+> g) <+> eprod (mult p q)      ... cong ((f <+> g) <+>) (ppm p q)

0 pnorm :  CommutativeMonoid a
        => (e : Expr a as)
        -> eval e === eterm (normalize e)
pnorm (Lit x) = Calc $
  |~ x
  ~~ x <+> neutral        ..< appendRightNeutral
  ~~ x <+> eprod {as} one ..< cong (x <+>) (pone as)

pnorm (Var x y) = Calc $
 |~ x
 ~~ eprod (fromVar y)             ..< pvar as y
 ~~ neutral <+> eprod (fromVar y) ..< appendLeftNeutral

pnorm Neutral = Calc $
  |~ neutral
  ~~ neutral <+> neutral        ..< appendRightNeutral
  ~~ neutral <+> eprod {as} one ..< cong (neutral <+>) (pone as)

pnorm (Append x y) = Calc $
  |~ eval x <+> eval y
  ~~ eterm (normalize x) <+> eval y
     ... cong (<+> eval y) (pnorm x)
  ~~ eterm (normalize x) <+> eterm (normalize y)
     ... cong (eterm (normalize x) <+>) (pnorm y)
  ~~ eterm (append (normalize x) (normalize y))
     ... pappend (normalize x) (normalize y)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

export
0 solve :  CommutativeMonoid a
        => (as : List a)
        -> (e1,e2 : Expr a as)
        -> (prf : normalize e1 === normalize e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ eterm (normalize e1) ... pnorm e1
  ~~ eterm (normalize e2) ... cong eterm prf
  ~~ eval e2              ..< pnorm e2
