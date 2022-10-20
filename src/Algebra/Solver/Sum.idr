module Algebra.Solver.Sum

import Algebra.Ring
import Algebra.Solver.Prod
import Syntax.PreorderReasoning

%default total

||| Normalized arithmetic expression in a commutative
||| ring (represented as an (ordered) sum of terms).
public export
data Sum : (a : Type) -> (as : List a) -> Type where
  Nil  : {0 as : List a} -> Sum a as
  (::) : {0 as : List a} -> Term a as -> Sum a as -> Sum a as

||| Evaluate a sum of terms.
public export
esum : Num a => {as : List a} -> Sum a as -> a
esum []        = 0
esum (x :: xs) = eterm x + esum xs

||| Negate a sum of terms.
public export
negate : Neg a => Sum a as -> Sum a as
negate []       = []
negate (x :: y) = negTerm x :: negate y

--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

||| Add two sums of terms.
|||
||| The order of terms will be kept. If two terms have identical
||| products of variables, they will be unified by adding their
||| factors.
public export
add : Num a => Sum a as -> Sum a as -> Sum a as
add []        ys                = ys
add xs        []                = xs
add (T m x :: xs) (T n y :: ys) = case compProd x y of
  LT => T m x :: add xs (T n y :: ys)
  GT => T n y :: add (T m x :: xs) ys
  EQ => T (m + n) y :: add xs ys

||| Normalize a sum of terms by removing all terms with a
||| `zero` factor.
public export
normSum : {num : _} -> SolvableNum a num => Sum a as -> Sum a as
normSum []           = []
normSum (T f p :: y) = case num_isZero f of
  Just refl => normSum y
  Nothing   => T f p :: normSum y

||| Multiplies a single term with a sum of terms.
public export
mult1 : Num a => Term a as -> Sum a as -> Sum a as
mult1 (T f p) (T g q :: xs) = T (f * g) (mult p q) :: mult1 (T f p) xs
mult1 _       []            = []

||| Multiplies two sums of terms.
public export
mult : Num a => Sum a as -> Sum a as -> Sum a as
mult []        ys = []
mult (x :: xs) ys = add (mult1 x ys) (mult xs ys)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

-- Adding two sums via `add` preserves the evaluation result.
export
0 padd :
     {num : _}
  -> Semiring a num
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
       ..< lemma213 @{SRPlusCSem}
    ~~ n * eprod y + esum (add (T m x :: xs) ys)
       ... cong (n * eprod y +) (padd (T m x :: xs) ys)

  _ | EQ = case pcompProd x y eq of
        Refl => Calc $
          |~ (m * eprod x + esum xs) + (n * eprod x + esum ys)
          ~~ (m * eprod x + n * eprod x) + (esum xs + esum ys)
             ... lemma1324 @{SRPlusCSem}
          ~~ (m + n) * eprod x + (esum xs + esum ys)
             ..< cong (+ (esum xs + esum ys)) rightDistributive
          ~~ (m + n) * eprod x + esum (add xs ys)
             ... cong ((m + n) * eprod x +) (padd xs ys)

-- Small utility lemma
0 psum0 :
     {num : _}
  -> Semiring a num
  => {x,y,z : a}
  -> x === y
  -> x === 0 * z + y
psum0 prf = Calc $
  |~ x
  ~~ y          ... prf
  ~~ 0 + y      ..< plusZeroLeftNeutral
  ~~ 0 * z + y  ..< cong (+ y) multZeroLeftAbsorbs

-- Multiplying a sum with a term preserves the evaluation result.
0 pmult1 :
     {num : _}
  -> Semiring a num
  => (m : a)
  -> (p : Prod a as)
  -> (s : Sum a as)
  -> esum (mult1 (T m p) s) === (m * eprod p) * esum s
pmult1 m p []            = sym multZeroRightAbsorbs
pmult1 m p (T n q :: xs) = Calc $
  |~ (m * n) * (eprod (mult p q)) + esum (mult1 (T m p) xs)
  ~~ (m * n) * (eprod p * eprod q) + esum (mult1 (T m p) xs)
     ..< cong (\x => (m*n) * x + esum (mult1 (T m p) xs)) (pemprod @{SRMultCMon} p q)
  ~~ (m * eprod p) * (n * eprod q) + esum (mult1 (T m p) xs)
     ..< cong (+ esum (mult1 (T m p) xs)) (lemma1324 @{SRMultCSem})
  ~~ (m * eprod p) * (n * eprod q) + (m * eprod p) * esum xs
     ... cong ((m * eprod p) * (n * eprod q) +) (pmult1 m p xs)
  ~~ (m * eprod p) * (n * eprod q + esum xs)
     ..< leftDistributive

||| Multiplying two sums of terms preserves the evaluation result.
export
0 pmult :
     {num : _}
  -> Semiring a num
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

||| Evaluating a negated sum of terms is equivalent to negate the
||| result of evaluating the sum of terms.
export
0 pneg :
     {neg : _}
  -> Ring a neg
  => (x : Sum a as)
  -> esum (negate x) === negate (esum x)
pneg []       = sym $ negZero
pneg (x :: y) = Calc $
  |~ eterm (negTerm x) + esum (negate y)
  ~~ negate (eterm x) + esum (negate y) ... cong (+ esum (negate y)) (pnegTerm x)
  ~~ negate (eterm x) + negate (esum y) ... cong (negate (eterm x) +) (pneg y)
  ~~ negate (eterm x + esum y)          ..< negDistributes

||| Removing zero values from a sum of terms does not
||| affect the evaluation result.
export
0 pnormSum :
     {num : _}
  -> SolvableNum a num
  => Semiring a num
  => (s : Sum a as)
  -> esum (normSum s) === esum s
pnormSum []           = Refl
pnormSum (T f p :: y) with (num_isZero f)
  _ | Nothing   = Calc $
    |~ f * eprod p + esum (normSum y)
    ~~ f * eprod p + esum y ... cong ((f * eprod p) +) (pnormSum y)

  _ | Just refl = Calc $
    |~ esum (normSum y)
    ~~ esum y               ... pnormSum y
    ~~ 0 + esum y           ..< plusZeroLeftNeutral
    ~~ 0 * eprod p + esum y ..< cong (+ esum y) multZeroLeftAbsorbs
    ~~ f * eprod p + esum y ..< cong (\x => x * eprod p + esum y) refl
