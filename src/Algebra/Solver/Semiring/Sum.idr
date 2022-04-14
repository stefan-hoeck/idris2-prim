module Algebra.Solver.Semiring.Sum

import Algebra.Solver.Semiring.Expr
import Algebra.Solver.Semiring.Prod
import Algebra.Solver.Semiring.SolvableSemiring
import Algebra.Solver.Semiring.Util

%default total

||| A single term in a normalized arithmetic expressions.
|||
||| This is a product of all variables each raised to
||| a given power, multiplied with a factors (which is supposed
||| to reduce during elaboration).
public export
record Term (a : Type) (as : List a) where
  constructor T
  factor : a
  prod   : Prod a as

||| Evaluate a term.
public export
eterm : Semiring a => {as : List a} -> Term a as -> a
eterm (T f p) = f * eprod p

||| Normalized arithmetic expression in a commutative
||| ring (represented as an (ordered) sum of terms).
public export
data Sum : (a : Type) -> (as : List a) -> Type where
  Nil  : {0 as : List a} -> Sum a as
  (::) : {0 as : List a} -> Term a as -> Sum a as -> Sum a as

||| Evaluate a sum of terms.
public export
esum : Semiring a => {as : List a} -> Sum a as -> a
esum []        = 0
esum (x :: xs) = eterm x + esum xs

--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

||| Add two sums of terms.
|||
||| The order of terms will be kept. If two terms have identical
||| products of variables, they will be unified by adding their
||| factors.
public export
add : SolvableSemiring a => Sum a as -> Sum a as -> Sum a as
add []        ys                = ys
add xs        []                = xs
add (T m x :: xs) (T n y :: ys) = case compProd x y of
  LT => T m x :: add xs (T n y :: ys)
  GT => T n y :: add (T m x :: xs) ys
  EQ => T (m + n) y :: add xs ys

||| Normalize a sum of terms by removing all terms with a
||| `zero` factor.
public export
normSum : SolvableSemiring a => Sum a as -> Sum a as
normSum []           = []
normSum (T f p :: y) = case isZero f of
  Just refl => normSum y
  Nothing   => T f p :: normSum y

||| Multiplies a single term with a sum of terms.
public export
mult1 : SolvableSemiring a => Term a as -> Sum a as -> Sum a as
mult1 (T f p) (T g q :: xs) = T (f * g) (mult p q) :: mult1 (T f p) xs
mult1 _       []            = []

||| Multiplies two sums of terms.
public export
mult : SolvableSemiring a => Sum a as -> Sum a as -> Sum a as
mult []        ys = []
mult (x :: xs) ys = add (mult1 x ys) (mult xs ys)

||| Normalizes an arithmetic expression to a sum of products.
public export
norm : SolvableSemiring a => {as : List a} -> Expr a as -> Sum a as
norm (Lit n)     = [T n one]
norm (Var x y)   = [T 1 $ fromVar y]
norm (Plus x y)  = add (norm x) (norm y)
norm (Mult x y)  = mult (norm x) (norm y)

||| Like `norm` but removes all `zero` terms.
public export
normalize : SolvableSemiring a => {as : List a} -> Expr a as -> Sum a as
normalize e = normSum (norm e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

-- Adding two sums via `add` preserves the evaluation result.
0 padd :  SolvableSemiring a
       => (x,y : Sum a as)
       -> esum x + esum y === esum (add x y)
padd []            xs = plusZeroLeftNeutral
padd (x :: xs)     [] = plusZeroRightNeutral
padd (T m x :: xs) (T n y :: ys) with (compProd x y) proof eq
  _ | LT = Calc $
    |~ (m * eprod x + esum xs) + (n * eprod y + esum ys)
    ~~ m * eprod x + (esum xs + (n * eprod y + esum ys))
       ..< plusAssociative
    ~~ m * eprod x + esum (add xs (T n y :: ys))
       ... cong (m * eprod x +) (padd xs (T n y :: ys))

  _ | GT = Calc $
    |~ (m * eprod x + esum xs) + (n * eprod y + esum ys)
    ~~ n * eprod y + ((m * eprod x + esum xs) + esum ys)
       ..< p213
    ~~ n * eprod y + esum (add (T m x :: xs) ys)
       ... cong (n * eprod y +) (padd (T m x :: xs) ys)

  _ | EQ = case pcompProd x y eq of
        Refl => Calc $
          |~ (m * eprod x + esum xs) + (n * eprod x + esum ys)
          ~~ (m * eprod x + n * eprod x) + (esum xs + esum ys)
             ... p1324
          ~~ (m + n) * eprod x + (esum xs + esum ys)
             ..< cong (+ (esum xs + esum ys)) rightDistributive
          ~~ (m + n) * eprod x + esum (add xs ys)
             ... cong ((m + n) * eprod x +) (padd xs ys)

-- Small utility lemma
0 psum0 :  SolvableSemiring a
        => {x,y,z : a}
        -> x === y
        -> x === 0 * z + y
psum0 prf = Calc $
  |~ x
  ~~ y          ... prf
  ~~ 0 + y      ..< plusZeroLeftNeutral
  ~~ 0 * z + y  ..< cong (+ y) multZeroLeftAbsorbs

-- Multiplying a sum with a term preserves the evaluation result.
0 pmult1 :  SolvableSemiring a
         => (m : a)
         -> (p : Prod a as)
         -> (s : Sum a as)
         -> esum (mult1 (T m p) s) === (m * eprod p) * esum s
pmult1 m p []            = sym multZeroRightAbsorbs
pmult1 m p (T n q :: xs) = Calc $
  |~ (m * n) * (eprod (mult p q)) + esum (mult1 (T m p) xs)
  ~~ (m * n) * (eprod p * eprod q) + esum (mult1 (T m p) xs)
     ... cong (\x => (m*n) * x + esum (mult1 (T m p) xs)) (pmult p q)
  ~~ (m * eprod p) * (n * eprod q) + esum (mult1 (T m p) xs)
     ..< cong (+ esum (mult1 (T m p) xs)) m1324
  ~~ (m * eprod p) * (n * eprod q) + (m * eprod p) * esum xs
     ... cong ((m * eprod p) * (n * eprod q) +) (pmult1 m p xs)
  ~~ (m * eprod p) * (n * eprod q + esum xs)
     ..< leftDistributive

-- Multiplying two sums of terms preserves the evaluation result.
0 pmult :  SolvableSemiring a
        => (x,y : Sum a as)
        -> esum x * esum y === esum (mult x y)
pmult []            y = multZeroLeftAbsorbs
pmult (T n x :: xs) y = Calc $
  |~ (n * eprod x + esum xs) * esum y
  ~~ (n * eprod x) * esum y + esum xs * esum y
     ... rightDistributive
  ~~ (n * eprod x) * esum y + esum (mult xs y)
     ... cong ((n * eprod x) * esum y +) (pmult xs y)
  ~~ esum (mult1 (T n x) y) + esum (mult xs y)
     ..< cong (+ esum (mult xs y)) (pmult1 n x y)
  ~~ esum (add (mult1 (T n x) y) (mult xs y))
     ... padd (mult1 (T n x) y) (mult xs y)

-- Removing zero values from a sum of terms does not
-- affect the evaluation result.
0 pnormSum :  SolvableSemiring a
           => (s : Sum a as)
           -> esum (normSum s) === esum s
pnormSum []           = Refl
pnormSum (T f p :: y) with (isZero f)
  _ | Nothing   = Calc $
    |~ f * eprod p + esum (normSum y)
    ~~ f * eprod p + esum y ... cong ((f * eprod p) +) (pnormSum y)

  _ | Just refl = Calc $
    |~ esum (normSum y)
    ~~ esum y               ... pnormSum y
    ~~ 0 + esum y           ..< plusZeroLeftNeutral
    ~~ 0 * eprod p + esum y ..< cong (+ esum y) multZeroLeftAbsorbs
    ~~ f * eprod p + esum y ..< cong (\x => x * eprod p + esum y) refl

-- Evaluating an expression gives the same result as
-- evaluating its normalized form.
0 pnorm :  SolvableSemiring a
        => (e : Expr a as)
        -> eval e === esum (norm e)
pnorm (Lit n)    = Calc $
  |~ n
  ~~ n * 1                    ..< multOneRightNeutral
  ~~ n * eprod (one {as})     ..< cong (n *) (pone as)
  ~~ n * eprod (one {as}) + 0 ..< plusZeroRightNeutral

pnorm (Var x y)  = Calc $
  |~ x
  ~~ eprod (fromVar y)          ..< pvar as y
  ~~ 1 * eprod (fromVar y)      ..< multOneLeftNeutral
  ~~ 1 * eprod (fromVar y) + 0  ..< plusZeroRightNeutral

pnorm (Plus x y) = Calc $
  |~ eval x + eval y
  ~~ esum (norm x) + eval y
     ... cong (+ eval y) (pnorm x)
  ~~ esum (norm x) + esum (norm y)
     ... cong (esum (norm x) +) (pnorm y)
  ~~ esum (add (norm x) (norm y))
     ... padd _ _

pnorm (Mult x y) = Calc $
  |~ eval x * eval y
  ~~ esum (norm x) * eval y
     ... cong (* eval y) (pnorm x)
  ~~ esum (norm x) * esum (norm y)
     ... cong (esum (norm x) *) (pnorm y)
  ~~ esum (mult (norm x) (norm y))
     ... Sum.pmult _ _

-- Evaluating an expression gives the same result as
-- evaluating its normalized form.
0 pnormalize :  SolvableSemiring a
             => (e : Expr a as)
             -> eval e === esum (normalize e)
pnormalize e = Calc $
  |~ eval e
  ~~ esum (norm e)           ... pnorm e
  ~~ esum (normSum (norm e)) ..< pnormSum (norm e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

||| Given a list `as` of variables and two arithmetic expressions
||| over these variables, if the expressions are converted
||| to the same normal form, evaluating them gives the same
||| result.
|||
||| This simple fact allows us to conveniently and quickly
||| proof arithmetic equalities required in other parts of
||| our code. For instance:
|||
||| ```idris example
||| 0 binom1 : {x,y : Bits8}
|||          -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
||| binom1 = solve [x,y]
|||                ((x .+. y) * (x .+. y))
|||                (x .*. x + 2 *. x *. y + y .*. y)
||| ```
export
0 solve :  SolvableSemiring a
        => (as : List a)
        -> (e1,e2 : Expr a as)
        -> (prf : normalize e1 === normalize e2)
        => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normalize e1) ...(pnormalize e1)
  ~~ esum (normalize e2) ...(cong esum prf)
  ~~ eval e2             ..<(pnormalize e2)
