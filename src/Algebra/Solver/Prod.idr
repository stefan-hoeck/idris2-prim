module Algebra.Solver.Prod

import Algebra.Ring
import public Data.List.Elem
import Syntax.PreorderReasoning

%default total

||| A product of variables each represented by the exponent,
||| to which it is raised.
|||
||| When normalizing commutative arithmetic expressions, they often
||| get converted to (sums of) products of variables
||| (listed in index `as`), each raised to a certain
||| exponent. This is the case for commutative monoids
||| (a single product) as well as commutative (semi)rings
||| (a sum of products).
public export
data Prod : (a : Type) -> (as : List a) -> Type where
  Nil  : Prod a []
  (::) : (exp : Nat) -> Prod a xs -> Prod a (x :: xs)

||| Multiplying two products means adding all
||| expontents pairwise.
public export
mult : Prod a as -> Prod a as -> Prod a as
mult []        []        = []
mult (x :: xs) (y :: ys) = (x + y) :: mult xs ys

||| We sort products by lexicographically comparing
||| the exponents.
public export
compProd : Prod a as -> Prod a as -> Ordering
compProd []        []        = EQ
compProd (x :: xs) (y :: ys) = case compare x y of
  LT => LT
  GT => GT
  EQ => compProd xs ys

||| The neutral product where all exponents are zero.
public export
one : {as : List a} -> Prod a as
one {as = []}      = []
one {as = x :: xs} = 0 :: one

||| Convert a single variable to a product of variables.
public export
fromVar : {as : List a} -> Elem x as -> Prod a as
fromVar {as = x :: xs} Here      = 1 :: one
fromVar {as = x :: xs} (There y) = 0 :: fromVar y
fromVar {as = []} Here impossible
fromVar {as = []} (There y) impossible

--------------------------------------------------------------------------------
--          Term
--------------------------------------------------------------------------------

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

||| Negate a term.
public export
negTerm : Neg a => Term a as -> Term a as
negTerm (T f p) = T (negate f) p

public export
append : Semigroup a => Term a as -> Term a as -> Term a as
append (T f1 p1) (T f2 p2) = T (f1 <+> f2) (mult p1 p2)

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

public export
times : Monoid a => Nat -> a -> a
times 0     x = neutral
times (S k) x = x <+> times k x

||| Multiplies a value `n` times with itself. In case of `n`
||| being zero, this returns `1`.
public export %inline
pow : Num a => Nat -> a -> a
pow = times @{MultMon}

public export
emprod : Monoid a => {as : List a} -> Prod a as -> a
emprod []                        = neutral
emprod {as = v :: vs} (exp :: x) = times exp v <+> emprod x

||| Evaluate products of variables each raised to
||| given exponent.
|||
||| Every arithmetic expression in a commutative ring
||| can be represented as a sum of products of the variables
||| each raised by an exponent and multiplied by a constant
||| factor. For instance, expression `x + x * (y + z + z)`
||| gets normalized to `x + x * y + 2 * x * z`.
public export %inline
eprod : Num a => {as : List a} -> Prod a as -> a
eprod = emprod @{MultMon}

||| Evaluate a term using the given monoid.
public export
emterm : Monoid a => {as : List a} -> Term a as -> a
emterm (T f p) = f <+> emprod p

||| Evaluate a term using multiplication.
public export %inline
eterm : Num a => {as : List a} -> Term a as -> a
eterm = emterm @{MultMon}

--------------------------------------------------------------------------------
--          Monoid Proofs
--------------------------------------------------------------------------------

export
0 ptimes :
     {mon : _}
  -> CommutativeMonoid a mon
  => (m,n : Nat)
  -> (x : a)
  -> times m x <+> times n x === times (m + n) x
ptimes 0     n x = appendLeftNeutral
ptimes (S k) n x = Calc $
  |~ (x <+> times k x) <+> times n x
  ~~ x <+> (times k x <+> times n x) ..< appendAssociative
  ~~ x <+> times (k + n) x           ... cong (x <+>) (ptimes k n x)

export
0 pemprod :
     {mon : _}
  -> CommutativeMonoid a mon
  => (e1,e2 : Prod a as)
  -> emprod e1 <+> emprod e2 === emprod (mult e1 e2)
pemprod []        []        = appendRightNeutral
pemprod {as = v :: vs} (m :: xs) (n :: ys) = Calc $
  |~ (times m v <+> emprod xs) <+> (times n v <+> emprod ys)
  ~~ (times m v <+> times n v) <+> (emprod xs <+> emprod ys)
     ... lemma1324 @{CMonCSem}
  ~~ (times m v <+> times n v) <+> emprod (mult xs ys)
     ... cong ((times m v <+> times n v) <+>) (pemprod xs ys)
  ~~ times (m + n) v <+> emprod (mult xs ys)
     ... cong (<+> emprod (mult xs ys)) (ptimes m n v)

export
0 pappend :
     {mon : _}
  -> CommutativeMonoid a mon
  => (e1,e2 : Term a as)
  -> emterm e1 <+> emterm e2 === emterm (append e1 e2)
pappend (T f p) (T g q) = Calc $
  |~ (f <+> emprod p) <+> (g <+> emprod q)
  ~~ (f <+> g) <+> (emprod p <+> emprod q) ... lemma1324
  ~~ (f <+> g) <+> emprod (mult p q)       ... cong ((f <+> g) <+>) (pemprod p q)

||| Proof that `Prod.one` evaluates to `neutral`
export
0 pone :
     {mon : _}
  -> CommutativeMonoid a mon
  => (as : List a)
  -> emprod {as} Prod.one === Prelude.neutral
pone []        = Refl
pone (v :: vs) = Calc $
  |~ neutral <+> emprod {as = vs} one
  ~~ neutral <+> neutral             ... cong (neutral <+>) (pone vs)
  ~~ neutral                         ... appendLeftNeutral

||| Proof that for `e : Elem x as`, `fromVar e` evaluates to `x`.
export
0 pvar :
     {mon : _}
  -> CommutativeMonoid a mon
  => (as : List a)
  -> (e  : Elem x as)
  -> emprod (fromVar {as} e) === x
pvar (x :: vs) Here      = Calc $
  |~ (x <+> neutral) <+> emprod {as = vs} one
  ~~ (x <+> neutral) <+> neutral ... cong ((x <+> neutral) <+>) (pone vs)
  ~~ x <+> neutral               ... appendRightNeutral
  ~~ x                           ... appendRightNeutral

pvar (v :: vs) (There y) = Calc $
  |~ neutral <+> emprod (fromVar y)
  ~~ emprod (fromVar y)            ... appendLeftNeutral
  ~~ x                             ... pvar vs y

pvar [] Here impossible
pvar [] (There y) impossible

--------------------------------------------------------------------------------
--          Ordering Proofs
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

--------------------------------------------------------------------------------
--          Ring Proofs
--------------------------------------------------------------------------------

||| Evaluating a negated term is equivalent to negate the
||| result of evaluating the term.
export
0 pnegTerm :
     {neg : _}
  -> Ring a neg
  => (x : Term a as)
  -> eterm (negTerm x) === negate (eterm x)
pnegTerm (T f p) = multNegLeft
