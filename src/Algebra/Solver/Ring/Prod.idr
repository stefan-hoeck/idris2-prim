module Algebra.Solver.Ring.Prod

import Algebra.Solver.Ring.Expr
import Algebra.Solver.Ring.Util

%default total

public export
data Prod : (a : Type) -> (as : List a) -> Type where
  Nil  : Prod a []
  (::) : (exp : Nat) -> Prod a xs -> Prod a (x :: xs)

public export
merge : Prod a as -> Prod a as -> Prod a as
merge []        []        = []
merge (x :: xs) (y :: ys) = (x + y) :: merge xs ys

public export
eprod : Ring a => {as : List a} -> Prod a as -> a
eprod {as = []}      []        = 1
eprod {as = x :: xs} (e :: es) = pow x e * eprod es

public export
compProd : Prod a as -> Prod a as -> Ordering
compProd []        []        = EQ
compProd (x :: xs) (y :: ys) = case compare x y of
  LT => LT
  GT => GT
  EQ => compProd xs ys

public export
one : {as : List a} -> Prod a as
one {as = []}      = []
one {as = x :: xs} = 0 :: one

public export
fromVar : {as : List a} -> Elem x as -> Prod a as
fromVar {as = x :: xs} Here      = 1 :: one
fromVar {as = x :: xs} (There y) = 0 :: fromVar y
fromVar {as = []} Here impossible
fromVar {as = []} (There y) impossible

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

Uninhabited (LT = EQ) where
  uninhabited _ impossible

Uninhabited (GT = EQ) where
  uninhabited _ impossible

export
0 pcompNat : (x,y : Nat) -> (compare x y === EQ) -> x === y
pcompNat 0 0         prf = Refl
pcompNat (S k) (S j) prf = cong S $ pcompNat k j prf
pcompNat 0 (S k) Refl impossible
pcompNat (S k) 0 Refl impossible

export
0 pcompProd :  (x,y : Prod a as)
            -> (compProd x y === EQ)
            -> x === y
pcompProd []        []        prf = Refl
pcompProd (x :: xs) (y :: ys) prf with (compare x y) proof eq
  _ | EQ = cong2 (::) (pcompNat x y eq) (pcompProd xs ys prf)
  _ | LT = absurd prf
  _ | GT = absurd prf
pcompProd []        (_ :: _)  Refl impossible
pcompProd (_ :: _)  []        Refl impossible

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
