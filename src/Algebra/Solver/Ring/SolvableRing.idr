module Algebra.Solver.Ring.SolvableRing

import Algebra.Ring

%default total

public export
interface Ring a => SolvableRing a where
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
