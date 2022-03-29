module Algebra.Solver.Ring.Sum

import Algebra.Solver.Ring.Expr
import Algebra.Solver.Ring.Prod
import Algebra.Solver.Ring.Util

%default total

public export
record Term (a : Type) (as : List a) where
  constructor T
  factor : a
  prod   : Prod a as

public export
eterm : RingLaws a => {as : List a} -> Term a as -> a
eterm (T f p) = f * eprod p

public export
negTerm : RingLaws a => Term a as -> Term a as
negTerm (T f p) = T (negate f) p

public export
data Sum : (a : Type) -> (as : List a) -> Type where
  Nil  : {0 as : List a} -> Sum a as
  (::) : {0 as : List a} -> Term a as -> Sum a as -> Sum a as

public export
esum : RingLaws a => {as : List a} -> Sum a as -> a
esum []        = 0
esum (x :: xs) = eterm x + esum xs

public export
negate : RingLaws a => Sum a as -> Sum a as
negate []       = []
negate (x :: y) = negTerm x :: negate y


--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

public export
add : Num a => Sum a as -> Sum a as -> Sum a as
add []        ys                = ys
add xs        []                = xs
add (T m x :: xs) (T n y :: ys) = case compProd x y of
  LT => T m x :: add xs (T n y :: ys)
  GT => T n y :: add (T m x :: xs) ys
  EQ => T (m + n) y :: add xs ys

public export
mult1 : Num a => Term a as -> Sum a as -> Sum a as
mult1 (T f p) (T g q :: xs) = T (f * g) (merge p q) :: mult1 (T f p) xs
mult1 _       []            = []

public export
mult : Num a => Sum a as -> Sum a as -> Sum a as
mult []        ys = []
mult (x :: xs) ys = add (mult1 x ys) (mult xs ys)

public export
normalize : RingLaws a => {as : List a} -> Expr a as -> Sum a as
normalize (Lit n)     = [T n one]
normalize (Var x y)   = [T 1 $ fromVar y]
normalize (Neg x)     = negate $ normalize x
normalize (Plus x y)  = add (normalize x) (normalize y)
normalize (Mult x y)  = mult (normalize x) (normalize y)
normalize (Minus x y) = add (normalize x) (negate $ normalize y)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
0 padd : RingLaws a => (x,y : Sum a as) -> esum x + esum y === esum (add x y)
padd []            xs = plusZeroLeftNeutral _
padd (x :: xs)     [] = plusZeroRightNeutral _
padd (T m x :: xs) (T n y :: ys) with (compProd x y) proof eq
  _ | LT = Calc $
    |~ (m * eprod x + esum xs) + (n * eprod y + esum ys)
    ~~ m * eprod x + (esum xs + (n * eprod y + esum ys))
       ..<(plusAssociative _ _ _)
    ~~ m * eprod x + esum (add xs (T n y :: ys))
       ...(cong (m * eprod x +) $ padd xs (T n y :: ys))

  _ | GT = Calc $
    |~ (m * eprod x + esum xs) + (n * eprod y + esum ys)
    ~~ n * eprod y + ((m * eprod x + esum xs) + esum ys)
       ..<(p213)
    ~~ n * eprod y + esum (add (T m x :: xs) ys)
       ...(cong (n * eprod y +) $ padd (T m x :: xs) ys)

  _ | EQ = case pcompProd x y eq of
    Refl => Calc $
      |~ (m * eprod x + esum xs) + (n * eprod x + esum ys)
      ~~ (m * eprod x + n * eprod x) + (esum xs + esum ys)
         ...(p1324)
      ~~ (m + n) * eprod x + (esum xs + esum ys)
         ..<(cong (+ (esum xs + esum ys)) $ rightDistributive _ _ _)
      ~~ (m + n) * eprod x + esum (add xs ys)
         ...(cong ((m + n) * eprod x +) $ padd xs ys)

export
0 psum0 :  RingLaws a
        => {x,y,z : a}
        -> x === y
        -> x === 0 * z + y
psum0 prf = Calc $
  |~ x
  ~~ y          ...(prf)
  ~~ 0 + y      ..<(plusZeroLeftNeutral _)
  ~~ 0 * z + y  ..<(cong (+ y) $ multZeroLeftAbsorbs _)

export
0 pmult1 :  RingLaws a
         => (m : a)
         -> (p : Prod a as)
         -> (s : Sum a as)
         -> esum (mult1 (T m p) s) === (m * eprod p) * esum s
pmult1 m p []            = sym $ multZeroRightAbsorbs _
pmult1 m p (T n q :: xs) = Calc $
  |~ (m * n) * (eprod (merge p q)) + esum (mult1 (T m p) xs)
  ~~ (m * n) * (eprod p * eprod q) + esum (mult1 (T m p) xs)
     ...(cong (\x => (m*n) * x + esum (mult1 (T m p) xs)) $ pmerge p q)
  ~~ (m * eprod p) * (n * eprod q) + esum (mult1 (T m p) xs)
     ..<(cong (+ esum (mult1 (T m p) xs)) $ m1324)
  ~~ (m * eprod p) * (n * eprod q) + (m * eprod p) * esum xs
     ...( cong ((m * eprod p) * (n * eprod q) +) $ pmult1 m p xs)
  ~~ (m * eprod p) * (n * eprod q + esum xs)
     ..<(leftDistributive _ _ _)

export
0 pmult : RingLaws a => (x,y : Sum a as) -> esum x * esum y === esum (mult x y)
pmult []            y = multZeroLeftAbsorbs _
pmult (T n x :: xs) y = Calc $
  |~ (n * eprod x + esum xs) * esum y
  ~~ (n * eprod x) * esum y + esum xs * esum y
     ...(rightDistributive _ _ _)
  ~~ (n * eprod x) * esum y + esum (mult xs y)
     ...(cong ((n * eprod x) * esum y +) $ pmult xs y)
  ~~ esum (mult1 (T n x) y) + esum (mult xs y)
     ..<(cong (+ esum (mult xs y)) $ pmult1 n x y)
  ~~ esum (add (mult1 (T n x) y) (mult xs y))
     ...(padd (mult1 (T n x) y) (mult xs y))

export
0 pnegTerm :  RingLaws a
           => (x : Term a as)
           -> eterm (negTerm x) === neg (eterm x)
pnegTerm (T f p) = multNegLeft _ _

export
0 pneg : RingLaws a => (x : Sum a as) -> esum (negate x) === neg (esum x)
pneg []       = sym $ negZero
pneg (x :: y) = Calc $
  |~ eterm (negTerm x) + esum (negate y)
  ~~ neg (eterm x) + esum (negate y) ...(cong (+ esum (negate y)) $ pnegTerm x)
  ~~ neg (eterm x) + neg (esum y)    ...(cong (neg (eterm x) +) $ pneg y)
  ~~ neg (eterm x + esum y)          ..<(negDistributes)

export
0 pnormalize : RingLaws a => (e : Expr a as) -> eval e === esum (normalize e)
pnormalize (Lit n)    = Calc $
  |~ n
  ~~ n * 1                    ..<(multOneRightNeutral _)
  ~~ n * eprod (one {as})     ..<(cong (n *) $ pone as)
  ~~ n * eprod (one {as}) + 0 ..<(plusZeroRightNeutral _)

pnormalize (Var x y)  = Calc $
  |~ x
  ~~ eprod (fromVar y)          ..<(pvar as y)
  ~~ 1 * eprod (fromVar y)      ..<(multOneLeftNeutral _)
  ~~ 1 * eprod (fromVar y) + 0  ..<(plusZeroRightNeutral _)

pnormalize (Neg x) = Calc $
  |~ neg (eval x)
  ~~ neg (esum (normalize x))    ...(cong neg $ pnormalize x)
  ~~ esum (negate (normalize x)) ..<(pneg $ normalize x)

pnormalize (Plus x y) = Calc $
  |~ eval x + eval y
  ~~ esum (normalize x) + eval y
     ...(cong (+ eval y) $ pnormalize x)
  ~~ esum (normalize x) + esum (normalize y)
     ...(cong (esum (normalize x) +) $ pnormalize y)
  ~~ esum (add (normalize x) (normalize y))
     ...(padd _ _)

pnormalize (Mult x y) = Calc $
  |~ eval x * eval y
  ~~ esum (normalize x) * eval y
     ...(cong (* eval y) $ pnormalize x)
  ~~ esum (normalize x) * esum (normalize y)
     ...(cong (esum (normalize x) *) $ pnormalize y)
  ~~ esum (mult (normalize x) (normalize y))
     ...(pmult _ _)

pnormalize (Minus x y) = Calc $
  |~ eval x - eval y
  ~~ eval x + neg (eval y)
     ...(minusIsPlusNeg _ _)
  ~~ esum (normalize x) + neg (eval y)
     ...(cong (+ neg (eval y)) $ pnormalize x)
  ~~ esum (normalize x) + neg (esum (normalize y))
     ...(cong (\v => esum (normalize x) + neg v) $ pnormalize y)
  ~~ esum (normalize x) + esum (negate (normalize y))
     ..<(cong (esum (normalize x) +) $ pneg (normalize y))
  ~~ esum (add (normalize x) (negate (normalize y)))
     ...(padd _ _)
