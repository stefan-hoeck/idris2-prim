module Algebra.Solver.Ring.Prod

import Algebra.Solver.Ring.Expr
import public Algebra.Solver.Prod
import Algebra.Solver.Ring.Util

%default total

||| Every arithmetic expression in a commutative ring
||| can be represented as a sum of products of the variables
||| each raised by an exponent and multiplied by a constant
||| factor. For instance, expression `x + x * (y + z + z)`
||| gets normalized to `x + x * y + 2 * x * z`.
|||
||| This function evaluates individual products in such a sum.
public export
eprod : Ring a => {as : List a} -> Prod a as -> a
eprod {as = []}      []        = 1
eprod {as = x :: xs} (e :: es) = pow x e * eprod es

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
0 pone : Ring a => (as : List a) -> eprod (one {as}) === 1
pone []        = Refl
pone (x :: xs) = Calc $
  |~ 1 * eprod (one {as = xs})
  ~~ 1 * 1                     ... cong (1 * ) (pone xs)
  ~~ 1                         ... multOneRightNeutral

export
0 pvar :  Ring a
       => (as : List a)
       -> (e  : Elem x as)
       -> eprod (fromVar {as} e) === x
pvar (x :: vs) Here      = Calc $
  |~ (x * 1) * eprod (one {as = vs})
  ~~ (x * 1) * 1                     ... cong ((x*1) *) (pone vs)
  ~~ x * 1                           ... multOneRightNeutral
  ~~ x                               ... multOneRightNeutral

pvar (v :: vs) (There y) = Calc $
  |~ 1 * eprod (fromVar {as = vs} y)
  ~~ 1 * x                           ... cong (1*) (pvar vs y)
  ~~ x                               ... multOneLeftNeutral

pvar [] Here impossible
pvar [] (There y) impossible

export
0 pmerge :  Ring a
         => (p,q : Prod a as)
         -> eprod (merge p q) === eprod p * eprod q
pmerge []        []        = sym multOneLeftNeutral
pmerge {as = h :: t} (x :: xs) (y :: ys) = Calc $
  |~ pow h (x + y) * eprod (merge xs ys)
  ~~ (pow h x * pow h y) * eprod (merge xs ys)
     ... cong (* eprod (merge xs ys)) (ppow x y h)
  ~~ (pow h x * pow h y) * (eprod xs * eprod ys)
     ... cong ((pow h x * pow h y) *) (pmerge xs ys)
  ~~ (pow h x * eprod xs) * (pow h y * eprod ys)
     ... Util.m1324
