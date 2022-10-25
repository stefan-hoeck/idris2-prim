module Algebra.OrderedRing

import public Algebra.OrderedSemiring
import public Algebra.Ring

%default total

||| An ordered ring is a ring with a total ordering `lt` and two
||| additional laws:
|||
||| 1.  `x < y` => `x + z < y + z` for all `x`, `y`, `z`
|||
||| 2. `0 < n`, `k < m` => `n * k < n * m` for all `k`, `m`, `n`
public export
interface OrderedRing a (0 neg : Neg a) (0 lt : a -> a -> Type) | a where
  constructor MkOrderedRing

  0 orr : Ring a neg

  0 or_transLT : {k,m,n : a} -> lt k m -> lt m n -> lt k n

  0 or_plusLeftLT : {k,m,n : a} -> lt k m -> lt (n + k) (n + m)

  0 or_multGT : {k,m,n : a} -> lt 0 n -> lt k m -> lt (n * k) (n * m)

  or_trichotomy : (m,n : a) -> Trichotomy lt m n

public export %inline %hint
ROrdered : OrderedRing a neg lt => Total a lt
ROrdered = MkTotal (or_transLT {a}) or_trichotomy

public export %inline %hint
0 ORR : OrderedRing a neg lt => Ring a neg
ORR = orr

public export %inline %hint
0 OROSR : OrderedRing a neg lt => OrderedSemiring a (negNum neg) lt
OROSR = MkOrderedSemiring
  (RSR @{ORR})
  (or_transLT {a})
  (or_plusLeftLT {a})
  (or_multGT {a})
  (or_trichotomy {a})

public export %inline %hint
0 ORSR : OrderedRing a neg lt => Semiring a (negNum neg)
ORSR = OSSR @{OROSR}

--------------------------------------------------------------------------------
--          Addition Lemmata
--------------------------------------------------------------------------------

||| Subtracting a value does not affect an inequality.
export
0 minus :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt k m
  -> Rel b lt (k - n) (m - n)
minus rel = CalcAny $
  |~ k - n
  <~ k + negate n .=. minusIsPlusNeg @{ORR}
  <! m + negate n ... plusRight rel
  <~ m - n        .~. minusIsPlusNeg @{ORR}

||| Subtracting a value from a larger one
||| yields a positive result.
export
0 minusLT :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt k m
  -> Rel b lt 0 (m - k)
minusLT rel = CalcAny $
  |~ 0
  <~ k - k .~. minusSelfZero @{ORR}
  <! m - k ... minus rel

||| Subtracting a value from a smaller one
||| yields a negative result.
export
0 minusGT :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt k m
  -> Rel b lt (k - m) 0
minusGT rel = CalcAny $
  |~ k - m
  <! m - m ... minus rel
  <~ 0     .=. minusSelfZero @{ORR}

||| We can solve (in)equalities, where the same value has
||| been subtracted from both sides.
export
0 solveMinus :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt (k - n) (m - n)
  -> Rel b lt k m
solveMinus rel = solvePlusRight $ CalcAny $
  |~ k + negate n
  <~ k - n        .~. minusIsPlusNeg @{ORR}
  <! m - n        ... rel
  <~ m + negate n .=. minusIsPlusNeg @{ORR}

||| We can solve (in)equalities, with one side an addition
||| and the other equalling zero.
export
0 solvePlusRightZero :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt 0 (m + n)
  -> Rel b lt (negate n) m
solvePlusRightZero rel = solvePlusRight $ CalcAny $
  |~ negate n + n
  <~ 0            .=. plusNegLeftZero @{ORR}
  <! m + n        ... rel

||| We can solve (in)equalities, with one side an addition
||| and the other equalling zero.
export
0 solvePlusLeftZero :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt 0 (n + m)
  -> Rel b lt (negate n) m
solvePlusLeftZero rel = solvePlusRightZero $ CalcAny $
  |~ 0
  <! n + m ... rel
  <~ m + n .=. plusCommutative @{ORSR}

||| We can solve (in)equalities, with one side an addition
||| and the other equalling zero.
export
0 solveMinusZero :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt 0 (m - n)
  -> Rel b lt n m
solveMinusZero rel = solvePlusRight $ CalcAny $
  |~ n + negate n
  <~ 0            .=. plusNegRightZero @{ORR}
  <! m - n        ... rel
  <~ m + negate n .=. minusIsPlusNeg @{ORR}

--------------------------------------------------------------------------------
--          Negation in Inequalities
--------------------------------------------------------------------------------

||| Negating both sides inverts an inequality.
export
0 negate :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt m n
  -> Rel b lt (negate n) (negate m)
negate rel = solvePlusLeftZero $ CalcAny $
  |~ 0
  <! n - m        ... minusLT rel
  <~ n + negate m .=. minusIsPlusNeg @{ORR}

||| Negating both sides inverts an inequality.
export
0 negateNeg :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt (negate m) (negate n)
  -> Rel b lt n m
negateNeg rel = CalcAny $
  |~ n
  <~ negate (negate n) .~. negInvolutory @{ORR}
  <! negate (negate m) ... negate rel
  <~ m                 .=. negInvolutory @{ORR}

||| `negate` specialized to where one side equals zero.
export
0 negateZeroLT :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt 0 n
  -> Rel b lt (negate n) 0
negateZeroLT rel = CalcAny $
  |~ negate n
  <! negate 0 ... negate rel
  <~ 0        .=. negZero @{ORR}

||| `negate` specialized to where one side equals zero.
export
0 negateZeroGT :
     {neg : _}
  -> OrderedRing a neg lt
  => Rel b lt n 0
  -> Rel b lt 0 (negate n)
negateZeroGT rel = CalcAny $
  |~ 0
  <~ negate 0 .~. negZero @{ORR}
  <! negate n ... negate rel
