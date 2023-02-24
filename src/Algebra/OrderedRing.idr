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

--------------------------------------------------------------------------------
--          Multiplication in Inequalities
--------------------------------------------------------------------------------

||| Multiplication with a negative number inverts an inequality.
export
0 multNegLeft :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt k m
  -> Rel b lt (n * m) (n * k)
multNegLeft p rel = negateNeg $ CalcAny $
  |~ negate (n * k)
  <~ negate n * k   .~. multNegLeft @{ORR}
  <! negate n * m   ... multPosLeft (toLT $ negateZeroGT {a} $ LT p) rel
  <~ negate (n * m) .=. multNegLeft @{ORR}

||| Multiplication with a negative number inverts an inequality.
export
0 multNegRight :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt k m
  -> Rel b lt (m * n) (k * n)
multNegRight p rel = CalcAny $
  |~ m * n
  <~ n * m .=. multCommutative @{ORSR}
  <! n * k ... multNegLeft p rel
  <~ k * n .=. multCommutative @{ORSR}

||| Multiplication with a non-positive number inverts and
||| weakens an inequality.
export
0 multNonPosLeft :
     {num : _}
  -> OrderedRing a num lt
  => Rel b lt n 0
  -> lt k m
  -> Rel b lt (n * m) (n * k)
multNonPosLeft (LT p) y = multNegLeft p (LT y)
multNonPosLeft (EQ p) y = EQ $ Calc $
  |~ n * m
  ~~ 0 * m ... cong (*m) p
  ~~ 0     ... multZeroLeftAbsorbs @{ORSR}
  ~~ 0 * k ..< multZeroLeftAbsorbs @{ORSR}
  ~~ n * k ..< cong (*k) p

||| Multiplication with a non-positive number inverts and
||| weakens an inequality.
export
0 multNonPosRight :
     {num : _}
  -> OrderedRing a num lt
  => Rel b lt n 0
  -> lt k m
  -> Rel b lt (m * n) (k * n)
multNonPosRight rel p = CalcAny $
  |~ m * n
  <~ n * m .=. multCommutative @{ORSR}
  <! n * k ... multNonPosLeft rel p
  <~ k * n .=. multCommutative @{ORSR}

||| From `n * k < n * m` and `n < 0` follows `m < n`. Likewise for `<=`.
export
0 solveMultNegLeft :
     {num : _}
  -> OrderedRing a num lt
  => lt n 0
  -> Rel b lt (n * k) (n * m)
  -> Rel b lt m k
solveMultNegLeft q rel =
  let q' := toLT $ negateZeroGT {a} (LT q)
  in solveMultPosLeft q' $ CalcAny $
    |~ negate n * m
    <~ negate (n * m) .=. multNegLeft @{ORR}
    <! negate (n * k) ... negate rel
    <~ negate n * k   .~. multNegLeft @{ORR}

||| From `k * n < m * n` and `n < 0` follows `m < n`. Likewise for `<=`.
export
0 solveMultNegRight :
     {num : _}
  -> OrderedRing a num lt
  => lt n 0
  -> Rel b lt (k * n) (m * n)
  -> Rel b lt m k
solveMultNegRight q rel = solveMultNegLeft q $ CalcAny $
  |~ n * k
  <~ k * n .=. multCommutative @{ORSR}
  <! m * n ... rel
  <~ n * m .=. multCommutative @{ORSR}

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling zero.
export
0 solveMultNegRightZero :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt 0 (m * n)
  -> Rel b lt m 0
solveMultNegRightZero p rel = solveMultNegRight p $ CalcAny $
  |~ 0 * n
  <~ 0     .=. multZeroLeftAbsorbs @{ORSR}
  <! m * n ... rel

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling zero.
export
0 solveMultNegLeftZero :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt 0 (n * m)
  -> Rel b lt m 0
solveMultNegLeftZero p rel = solveMultNegLeft p $ CalcAny $
  |~ n * 0
  <~ 0     .=. multZeroRightAbsorbs @{ORSR}
  <! n * m ... rel

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling one.
export
0 solveMultNegRightOne :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt n (m * n)
  -> Rel b lt m 1
solveMultNegRightOne p rel = solveMultNegRight p $ CalcAny $
  |~ 1 * n
  <~ n     .=. multOneLeftNeutral @{ORSR}
  <! m * n ... rel

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling one.
export
0 solveMultNegLeftOne :
     {neg : _}
  -> OrderedRing a neg lt
  => lt n 0
  -> Rel b lt n (n * m)
  -> Rel b lt m 1
solveMultNegLeftOne p rel = solveMultNegLeft p $ CalcAny $
  |~ n * 1
  <~ n     .=. multOneRightNeutral @{ORSR}
  <! n * m ... rel
