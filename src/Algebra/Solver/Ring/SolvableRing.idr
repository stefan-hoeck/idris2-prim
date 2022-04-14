module Algebra.Solver.Ring.SolvableRing

import Algebra.Ring

%default total

||| When normalizing arithmetic expressions, we must
||| make sure that factors that evaluate to zero must
||| be removed from the sum of products.
|||
||| For instance, the following example only works,
||| if the term `0 * x * y` gets removed before comparing
||| the normalized sums:
|||
||| ```idris example
||| 0 binom3 : {x,y : Bits8} -> (x + y) * (x - y) === x * x - y * y
||| binom3 = solve [x,y] ((x .+. y) * (x .-. y)) (x .*. x - y .*. y)
||| ```
|||
||| Because we cannot directly use a (primitive) pattern match
||| without having a concrete type, we need this interface.
||| (We *could* use `DecEq`, but this is not publicly exported
||| for the primitives; probably for good reasons since it is
||| implemented using `believe_me`).
public export
interface Ring a => SolvableRing a where

  ||| Checks if a value is propositionally equal to zero.
  isZero : (v : a) -> Maybe (v === 0)

public export
SolvableRing Bits8 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Bits16 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Bits32 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Bits64 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Int8 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Int16 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Int32 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Int64 where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Int where
  isZero 0 = Just Refl
  isZero _ = Nothing

public export
SolvableRing Integer where
  isZero 0 = Just Refl
  isZero _ = Nothing
