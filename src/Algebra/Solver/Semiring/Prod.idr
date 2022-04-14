module Algebra.Solver.Semiring.Prod

import Algebra.Solver.Semiring.Expr
import public Algebra.Solver.Prod
import Algebra.Solver.Semiring.Util

%default total

||| Evaluate products of variables each raised to
||| given exponent.
|||
||| Every arithmetic expression in a commutative ring
||| can be represented as a sum of products of the variables
||| each raised by an exponent and multiplied by a constant
||| factor. For instance, expression `x + x * (y + z + z)`
||| gets normalized to `x + x * y + 2 * x * z`.
public export
eprod : Semiring a => {as : List a} -> Prod a as -> a
eprod {as = []}      []        = 1
eprod {as = x :: xs} (e :: es) = pow x e * eprod es

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

||| Proof that `one` evaluates to 1.
export
0 pone : Semiring a => (as : List a) -> eprod (one {as}) === 1
pone []        = Refl
pone (x :: xs) = Calc $
  |~ 1 * eprod (one {as = xs})
  ~~ 1 * 1                     ... cong (1 * ) (pone xs)
  ~~ 1                         ... multOneRightNeutral

||| Proof that `fromVar x` evaluates to `x`.
export
0 pvar :  Semiring a
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

||| Proof that evaluation of a multiplication of products
||| is the same as multiplying the results of evaluating each
||| of them.
export
0 pmult :  Semiring a
        => (p,q : Prod a as)
        -> eprod (mult p q) === eprod p * eprod q
pmult []        []        = sym multOneLeftNeutral
pmult {as = h :: t} (x :: xs) (y :: ys) = Calc $
  |~ pow h (x + y) * eprod (mult xs ys)
  ~~ (pow h x * pow h y) * eprod (mult xs ys)
     ... cong (* eprod (mult xs ys)) (ppow x y h)
  ~~ (pow h x * pow h y) * (eprod xs * eprod ys)
     ... cong ((pow h x * pow h y) *) (pmult xs ys)
  ~~ (pow h x * eprod xs) * (pow h y * eprod ys)
     ... Util.m1324

