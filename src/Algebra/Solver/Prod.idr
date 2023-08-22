module Algebra.Solver.Prod

import public Data.List.Elem

%default total

||| A product of variables each represented by the exponent,
||| to which it is raised.
|||
||| When normalizing arithmetic expressions, they often
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
0 pcompProd :
     (x,y : Prod a as)
  -> (compProd x y === EQ)
  -> x === y
pcompProd []        []        prf = Refl
pcompProd (x :: xs) (y :: ys) prf with (compare x y) proof eq
  _ | EQ = cong2 (::) (pcompNat x y eq) (pcompProd xs ys prf)
  _ | LT = absurd prf
  _ | GT = absurd prf
pcompProd []        (_ :: _)  Refl impossible
pcompProd (_ :: _)  []        Refl impossible
