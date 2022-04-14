||| Additional utilites for solving and deriving
||| (in)equalities in `Integer` arithmetics.
module Data.Prim.Integer.Extra

import public Data.Prim.Integer
import Syntax.PreorderReasoning

%default total

infixl 0  <>
prefix 1  |>
infix  1  ..., ..=, =.., =.=
infix  1  ~.., ..~, ~.~

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Allows us to commute addition on both sides of an inequality.
export
0 pairPlusCommutative :  {w,x,y,z : Integer}
                      -> (w + x === x + w, y + z === z + y)
pairPlusCommutative = (plusCommutative, plusCommutative)

||| Allows us to commute multiplication on both sides of an inequality.
export
0 pairMultCommutative :  {w,x,y,z : Integer}
                      -> (w * x === x * w, y * z === z * y)
pairMultCommutative = (multCommutative, multCommutative)

--------------------------------------------------------------------------------
--          Syntax for deriving (in)equalities
--------------------------------------------------------------------------------

||| Type describing a relation between two integers.
|||
||| This is used to solve integer (in)equalities with
||| a syntax that is similar to the one used for preorder
||| reasoning.
public export
data Rel :  (rel : Integer -> Integer -> Type)
         -> (x,y : Integer)
         -> Type where
  (<)   : (x,y : Integer) -> Rel (<)   x y
  (<=)  : (x,y : Integer) -> Rel (<=)  x y
  (===) : (x,y : Integer) -> Rel (===) x y
  (>=)  : (x,y : Integer) -> Rel (>=)  x y
  (>)   : (x,y : Integer) -> Rel (>)   x y

public export
0 rel : Rel r x y -> (u,v : Integer) -> Rel r u v
rel (_ < _)   u v = u < v
rel (_ <= _)  u v = u <= v
rel (_ === _) u v = u === v
rel (_ >= _)  u v = u >= v
rel (_ > _)   u v = u > v

||| Reversed function application.
export
App : a -> (a -> b) -> b
App x f = f x

||| The identity function for relations.
export
0 (|>) : Rel r x y -> r x y -> r x y
(|>) _ v = v

||| Reversed function composition.
export
0 (<>) : (a -> b) -> (b -> c) -> a -> c
(<>) f g = g . f

||| Thought bubble similar to the one used in
||| `Syntax.PreorderReasoning`.
export
0 (...) : Rel r x y -> (Rel r x y -> a -> r x y) -> a -> r x y
(...) r f = f r

||| Replace the right hand side of an (in)equality.
export
0 (..=) : Rel r x z -> (y === z) -> r x y -> r x z
(..=) _ prf v = replace {p = r x} prf v

||| Replace the right hand side of an (in)equality.
export
0 (..~) : Rel r x z -> (z === y) -> r x y -> r x z
(..~) r prf = r ..= sym prf

||| Replace the left hand side of an (in)equality.
export
0 (=..) : Rel r x z -> (y === x) -> r y z -> r x z
(=..) _ prf v = replace {p = \a => r a z} prf v

||| Replace the left hand side of an (in)equality.
export
0 (~..) : Rel r x z -> (x === y) -> r y z -> r x z
(~..) r prf = r =.. sym prf

||| Replace both sides of an (in)equality.
export
0 (=.=) : Rel r w z -> (x === w, y === z) -> r x y -> r w z
(=.=) _ (p1,p2) v = replace {p = r w} p2
                  $ replace {p = \a => r a y} p1 v

||| Replace both sides of an (in)equality.
export
0 (~.~) : Rel r w z -> (w === x, z === y) -> r x y -> r w z
(~.~) r (p1,p2) = r =.= (sym p1, sym p2)

--------------------------------------------------------------------------------
--          Addition in Inequalities
--------------------------------------------------------------------------------

||| Adding a value on the left does not affect an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> z + x < z + y ... plusLeft
||| ```
export
0 plusLeft :  {x,y,z : Integer}
           -> Rel r (z + x) (z + y)
           -> r x y
           -> r (z + x) (z + y)
plusLeft (_ < _)   v         = plusGT x y z v
plusLeft (_ <= _)  (Left v)  = Left $ plusGT x y z v
plusLeft (_ <= _)  (Right v) = Right $ cong (z +) v
plusLeft (_ === _) v         = cong (z +) v
plusLeft (_ >= _)  (Left v)  = Left $ plusGT y x z v
plusLeft (_ >= _)  (Right v) = Right $ cong (z +) v
plusLeft (_ > _)   v         = plusGT y x z v

||| Adding a value on the right does not affect an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> x + z < y + z ... plusRight
||| ```
export
0 plusRight :  {x,y,z : Integer}
            -> Rel r (x + z) (y + z)
            -> r x y
            -> r (x + z) (y + z)
plusRight w =
  |> rel w x y
  <> rel w (z + x) (z + y) ... plusLeft
  <> rel w (x + z) (y + z) =.= pairPlusCommutative

||| Subtracting a value does not affect an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> x - z < y - z ... minus
||| ```
export
0 minus :  {x,y,z : Integer}
        -> Rel r (x - z) (y - z)
        -> r x y
        -> r (x - z) (y - z)
minus r =
  |> rel r x y
  <> rel r (x + neg z) (y + neg z) ... plusRight
  <> rel r (x - z) (y - z)         ~.~ (minusIsPlusNeg, minusIsPlusNeg)

||| We can solve (in)equalities, where the same value has
||| been added on both sides.
|||
||| ```idris example
||| |> x + z < y + z
||| <> x     < y     ... solvePlusRight
||| ```
export
0 solvePlusRight :  {x,y,z : Integer}
                 -> Rel r x y
                 -> r (x + z) (y + z)
                 -> r x y
solvePlusRight r =
  |> rel r (x + z) (y + z)
  <> rel r ((x + z) - z) ((y + z - z)) ... minus
  <> rel r x y                         =.= (
       solve [x,z] ((x .+. z) -. z) (var x)
     , solve [y,z] ((y .+. z) -. z) (var y)
     )

||| We can solve (in)equalities, where the same value has
||| been added on both sides.
|||
||| ```idris example
||| |> z + x < z + x
||| <> x     < y     ... solvePlusLeft
||| ```
export
0 solvePlusLeft :  {x,y,z : Integer}
                -> Rel r x y
                -> r (z + x) (z + y)
                -> r x y
solvePlusLeft r =
  |> rel r (z + x) (z + y)
  <> rel r (x + z) (y + z) =.= pairPlusCommutative
  <> rel r x y             ... solvePlusRight

||| We can solve (in)equalities, where the same value has
||| been subtracted from both sides.
|||
||| ```idris example
||| |> x - z < y - z
||| <> x     < y     ... solveMinus
||| ```
export
0 solveMinus :  {x,y,z : Integer}
             -> Rel r x y
             -> r (x - z) (y - z)
             -> r x y
solveMinus r =
  |> rel r (x - z) (y - z)
  <> rel r ((x - z) + z) ((y - z) + z) ... plusRight
  <> rel r x y                         =.= (
       solve [x,z] ((x .-. z) +. z) (var x)
     , solve [y,z] ((y .-. z) +. z) (var y)
     )

||| We can solve (in)equalities, with one side an addition
||| and the other equalling zero.
|||
||| ```idris example
||| |> 0     < x + y
||| <> neg y < x     ... solvePlusRightZero
||| ```
export
0 solvePlusRightZero :  {x,y : Integer}
                     -> Rel r (neg y) x
                     -> r 0 (x + y)
                     -> r (neg y) x
solvePlusRightZero r =
  |> rel r 0 (x + y)
  <> rel r (0 - y) ((x + y) - y) ... minus
  <> rel r (neg y) x             =.= (
       solve [y]   (0 -. y) (neg (var y))
     , solve [x,y] ((x .+. y) -. y) (var x)
     )

||| We can solve (in)equalities, with one side an addition
||| and the other equalling the added value.
|||
||| ```idris example
||| |> y  < x + y
||| <> 0  < x     ... solvePlusRightSelf
||| ```
export
0 solvePlusRightSelf :  {x,y : Integer}
                     -> Rel r 0 x
                     -> r y (x + y)
                     -> r 0 x
solvePlusRightSelf r =
  |> rel r y (x + y)
  <> rel r (0 + y) (x + y) ~.. plusZeroLeftNeutral
  <> rel r 0 x             ... solvePlusRight

||| We can solve (in)equalities, with one side an addition
||| and the other equalling zero.
|||
||| ```idris example
||| |> 0     < x + y
||| <> neg x < y     ... solvePlusLeftZero
||| ```
export
0 solvePlusLeftZero :  {x,y : Integer}
                     -> Rel r (neg x) y
                     -> r 0 (x + y)
                     -> r (neg x) y
solvePlusLeftZero r =
  |> rel r 0 (x + y)
  <> rel r 0 (y + x)  ..= plusCommutative
  <> rel r (neg x) y  ... solvePlusRightZero

||| We can solve (in)equalities, with one side an addition
||| and the other equalling the added value.
|||
||| ```idris example
||| |> x  < x + y
||| <> 0  < y     ... solvePlusLeftSelf
||| ```
export
0 solvePlusLeftSelf :  {x,y : Integer}
                    -> Rel r 0 y
                    -> r x (x + y)
                    -> r 0 y
solvePlusLeftSelf r =
  |> rel r x (x + y)
  <> rel r (x + 0) (x + y) ~.. plusZeroRightNeutral
  <> rel r 0 y             ... solvePlusLeft

||| We can solve (in)equalities, with one side a subtraction
||| and the other equalling zero.
|||
||| ```idris example
||| |> 0 < x - y
||| <> y < x     ... solveMinusZero
||| ```
export
0 solveMinusZero : {x,y : Integer} -> Rel r y x -> r 0 (x - y) -> r y x
solveMinusZero r =
  |> rel r 0 (x - y)
  <> rel r (0 + y) ((x - y) + y) ... plusRight
  <> rel r y x                   =.= (
       solve [y]   (0 +. y) (var y)
     , solve [x,y] ((x .-. y) +. y) (var x)
     )

--------------------------------------------------------------------------------
--          Negation in Inequalities
--------------------------------------------------------------------------------

||| Negating both sides inverts an inequality.
|||
||| ```idris example
||| |> x     <= y
||| <> neg y <= neg x ... negate
||| ```
export
0 negate :  {x,y : Integer}
         -> Rel r (neg y) (neg x)
         -> r x y
         -> r (neg y) (neg x)
negate r =
  |> rel r x y
  <> rel r (x - (x + y)) (y - (x + y)) ... minus
  <> rel r (neg y) (neg x)             =.= (
       solve [x,y] (x .- (x .+. y)) (negate $ var y)
     , solve [x,y] (y .- (x .+. y)) (negate $ var x)
     )

||| Negating both sides inverts an inequality.
|||
||| ```idris example
||| |> neg x <= neg y
||| <> y     <= x     ... negateNeg
||| ```
export
0 negateNeg : {x,y : Integer} -> Rel r y x -> r (neg x) (neg y) -> r y x
negateNeg r =
  |> rel r (neg x) (neg y)
  <> rel r (neg $ neg y) (neg $ neg x) ... negate
  <> rel r y x                         =.= (negInvolutory, negInvolutory)

||| `negate` specialized to where one side equals zero.
|||
||| ```idris example
||| |> x < 0
||| <> 0 < neg x ... negateZero
||| ```
|||
||| ```idris example
||| |> x <= 0
||| <> 0 <= neg x ... negateZero
||| ```
export
0 negateZero : {x : Integer} -> Rel r (neg x) 0 -> r 0 x -> r (neg x) 0
negateZero r =
  |> rel r 0 x
  <> rel r (neg x) (neg 0) ... negate
  <> rel r (neg x) 0       ..= negZero

||| `negate` specialized to where one side equals zero and the other
||| a negated value.
|||
||| ```idris example
||| |> neg x < 0
||| <> 0     < x ... negateNegZero
||| ```
|||
||| ```idris example
||| |> neg x <= 0
||| <> 0     <= x ... negateNegZero
||| ```
export
0 negateNegZero : {x : Integer} -> Rel r x 0 -> r 0 (neg x) -> r x 0
negateNegZero r =
  |> rel r 0             (neg x)
  <> rel r (neg (neg x)) (neg 0) ... negate
  <> rel r x 0                   =.= (negInvolutory, negZero)

--------------------------------------------------------------------------------
--          Multiplication in Inequalities
--------------------------------------------------------------------------------

0 mplLemma :  {x,y,z : Integer}
           -> 0 < z
           -> x < y
           -> z * x < z * y
mplLemma p =
  |> x         < y
  <> x - x     < y - x               ... minus
  <> 0         < y - x               =.. minusSelfZero
  <> 0         < z * (y - x)         ... (\_ => multPosPosGT0 _ _ p)
  <> 0 + z * x < z * (y - x) + z * x ... plusRight
  <> z * x     < z * y               =.= (
       solve [x,z]   (0 + z .*. x) (z .*. x)
     , solve [x,y,z] (z .* (y .-. x) + z .*. x) (z .*. y)
     )

||| Multiplication with a positive number preserves an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> z * x < z * y ... multPosLeft zgt0
||| ```
|||
||| ```idris example
||| |> x     <= y
||| <> z * x <= z * y ... multPosLeft zgt0
||| ```
export
0 multPosLeft :  {x,y,z : Integer}
              -> 0 < z
              -> Rel r (z * x) (z * y)
              -> r x y
              -> r (z * x) (z * y)
multPosLeft p (_ < _)   rxy       = mplLemma p rxy
multPosLeft p (_ <= _)  (Left w)  = Left $ mplLemma p w
multPosLeft p (_ <= _)  (Right w) = Right $ cong (z *) w
multPosLeft p (_ === _) rxy       = cong (z *) rxy
multPosLeft p (_ >= _)  (Left w)  = Left $ mplLemma p w
multPosLeft p (_ >= _)  (Right w) = Right $ cong (z *) w
multPosLeft p (_ > _)   rxy       = mplLemma p rxy

||| Multiplication with a positive number preserves an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> x * z < y * z ... multPosRight zgt0
||| ```
|||
||| ```idris example
||| |> x     <= y
||| <> x * z <= y * z ... multPosRight zgt0
||| ```
export
0 multPosRight :  {x,y,z : Integer}
               -> 0 < z
               -> Rel r (x * z) (y * z)
               -> r x y
               -> r (x * z) (y * z)
multPosRight p r =
  |> rel r x y
  <> rel r (z * x) (z * y) ... multPosLeft p
  <> rel r (x * z) (y * z) =.= pairMultCommutative

||| Multiplication with a negative number reverses an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> z * y < z * x ... multNegLeft zgt0
||| ```
|||
||| ```idris example
||| |> x     <= y
||| <> z * y <= z * x ... multNegLeft zgt0
||| ```
export
0 multNegLeft :  {x,y,z : Integer}
              -> z < 0
              -> Rel r (z * y) (z * x)
              -> r x y
              -> r (z * y) (z * x)
multNegLeft p r =
  let negp = negateZero (neg z > 0) p
   in |> rel r x y
      <> rel r (neg y) (neg x)                 ... negate
      <> rel r (neg z * neg y) (neg z * neg x) ... multPosLeft negp
      <> rel r (z * y) (z * x)                 =.= (
           solve [z,y] (neg (var z) * neg (var y)) (z .*. y)
         , solve [z,x] (neg (var z) * neg (var x)) (z .*. x)
         )

||| Multiplication with a negative number reverses an inequality.
|||
||| ```idris example
||| |> x     < y
||| <> y * z < x * z ... multNegRight zgt0
||| ```
|||
||| ```idris example
||| |> x     <= y
||| <> y * z <= x * z ... multNegRight zgt0
||| ```
export
0 multNegRight :  {x,y,z : Integer}
               -> z < 0
               -> Rel r (y * z) (x * z)
               -> r x y
               -> r (y * z) (x * z)
multNegRight p r =
  |> rel r x y
  <> rel r (z * y) (z * x) ... multNegLeft p
  <> rel r (y * z) (x * z) =.= pairMultCommutative

0 lemmaMult0 : {x,y,z : Integer} -> 0 === z -> x * z === y * z
lemmaMult0 prf = Calc $
  |~ x * z
  ~~ x * 0 ..< cong (x *) prf
  ~~ 0     ... multZeroRightAbsorbs
  ~~ y * 0 ..< multZeroRightAbsorbs
  ~~ y * z ... cong (y *) prf

||| Multiplication with a non-negative number weakens an inequality.
|||
||| ```idris example
||| |> x     <  y
||| <> x * z <= y * z ... multNonNegRight zgte0
||| ```
export
0 multNonNegRight :  {x,y,z : Integer}
                  -> 0 <= z
                  -> Rel (<=) (x * z) (y * z)
                  -> x < y
                  -> x * z <= y * z
multNonNegRight (Left p) r xy = Left $ multPosRight p (x * z < y * z) xy
multNonNegRight (Right p) r xy = Right $ lemmaMult0 p

||| Multiplication with a non-negative number weakens an inequality.
|||
||| ```idris example
||| |> x     <  y
||| <> z * x <= z * y ... multNonNegLeft zgte0
||| ```
export
0 multNonNegLeft :  {x,y,z : Integer}
                 -> 0 <= z
                 -> Rel (<=) (z * x) (z * y)
                 -> x < y
                 -> z * x <= z * y
multNonNegLeft p r =
  |> x < y
  <> x * z <= y * z ... multNonNegRight p
  <> z * x <= z * y =.= pairMultCommutative

||| Multiplication with a non-positive number weakens and
||| reverses an inequality.
|||
||| ```idris example
||| |> x     <  y
||| <> y * z <= x * z ... multNonPosRight zgte0
||| ```
export
0 multNonPosRight :  {x,y,z : Integer}
                  -> z <= 0
                  -> Rel (<=) (y * z) (x * z)
                  -> x < y
                  -> y * z <= x * z
multNonPosRight (Left p) r xy = Left $ multNegRight p (y * z < x * z) xy
multNonPosRight (Right p) r xy = Right $ lemmaMult0 (sym p)

||| Multiplication with a non-positive number weakens and
||| reverses an inequality.
|||
||| ```idris example
||| |> x     <  y
||| <> z * y <= z * x ... multNonPosLeft zlte0
||| ```
export
0 multNonPosLeft :  {x,y,z : Integer}
                 -> z <= 0
                 -> Rel (<=) (z * y) (z * x)
                 -> x < y
                 -> z * y <= z * x
multNonPosLeft p r =
  |> x < y
  <> y * z <= x * z ... multNonPosRight p
  <> z * y <= z * x =.= pairMultCommutative

0 smpLemma1 : {d,x,y : Integer} -> 0 < d -> d * x < d * y -> x < y
smpLemma1 dpos lt = case comp x y of
  LT p _ _ => p
  EQ _ p _ => void (EQ_not_LT (cong (d *) p) lt)
  GT _ _ p => void (GT_not_LT (multPosLeft dpos (d * x > d * y) p) lt)

0 smpLemma2 : {d,x,y : Integer} -> 0 < d -> d * x === d * y -> x === y
smpLemma2 dpos lt = case comp x y of
  LT p _ _ => void (LT_not_EQ (multPosLeft dpos (d * x < d * y) p) lt)
  EQ _ p _ => p
  GT _ _ p => void (GT_not_EQ (multPosLeft dpos (d * x > d * y) p) lt)

||| We can solve (in)equalities, where both sides have
||| been multiplied with the same positive value.
|||
||| ```idris example
||| |> z * x < z * y
||| <> x     < y     ... solveMultPosLeft zgt0
||| ```
export
0 solveMultPosLeft :  {d,x,y : Integer}
                   -> 0 < d
                   -> Rel r x y
                   -> r (d * x) (d * y)
                   -> r x y
solveMultPosLeft dpos (x < y)   lt         = smpLemma1 dpos lt
solveMultPosLeft dpos (x <= y)  (Left lt)  = Left $ smpLemma1 dpos lt
solveMultPosLeft dpos (x <= y)  (Right eq) = Right $ smpLemma2 dpos eq
solveMultPosLeft dpos (x === y) eq         = smpLemma2 dpos eq
solveMultPosLeft dpos (x >= y)  (Left lt)  = Left $ smpLemma1 dpos lt
solveMultPosLeft dpos (x >= y)  (Right eq) = Right $ smpLemma2 dpos eq
solveMultPosLeft dpos (x > y)   lt         = smpLemma1 dpos lt

||| We can solve (in)equalities, where both sides have
||| been multiplied with the same positive value.
|||
||| ```idris example
||| |> x * z < y * z
||| <> x     < y     ... solveMultPosRight zgt0
||| ```
export
0 solveMultPosRight :  {x,y,d : Integer}
                    -> 0 < d
                    -> Rel r x y
                    -> r (x * d) (y * d)
                    -> r x y
solveMultPosRight dpos r =
  |> rel r (x * d) (y * d)
  <> rel r (d * x) (d * y) =.= pairMultCommutative
  <> rel r x       y       ... solveMultPosLeft dpos

||| We can solve (in)equalities, where both sides have
||| been multiplied with the same negative value.
|||
||| ```idris example
||| |> z * x < z * y
||| <> y     < x     ... solveMultNegLeft zlt0
||| ```
export
0 solveMultNegLeft :  {d,x,y : Integer}
                   -> d < 0
                   -> Rel r y x
                   -> r (d * x) (d * y)
                   -> r y x
solveMultNegLeft dneg r =
  let negdPos = negateZero (neg d > 0) dneg
   in |> rel r (d * x) (d * y)
      <> rel r (neg (d * y)) (neg (d * x)) ... negate
      <> rel r (neg d * y) (neg d * x)     =.= (
           solve [d,y] (neg (d .*. y)) (neg (var d) *. y)
         , solve [d,x] (neg (d .*. x)) (neg (var d) *. x)
         )
      <> rel r y x ... solveMultPosLeft negdPos

||| We can solve (in)equalities, where both sides have
||| been multiplied with the same negative value.
|||
||| ```idris example
||| |> x * z < y * z
||| <> y     < y     ... solveMultNegLeft zlt0
||| ```
export
0 solveMultNegRight :  {x,y,d : Integer}
                    -> d < 0
                    -> Rel r y x
                    -> r (x * d) (y * d)
                    -> r y x
solveMultNegRight dneg r =
  |> rel r (x * d) (y * d)
  <> rel r (d * x) (d * y) =.= pairMultCommutative
  <> rel r y       x       ... solveMultNegLeft dneg

||| We can solve (in)equalities, with one side a multiplication
||| with a positive number and the other equalling zero.
|||
||| ```idris example
||| |> 0 < x * y
||| <> 0 < x     ... solveMultPosRightZero ygt0
||| ```
export
0 solveMultPosRightZero :  {x,y : Integer}
                        -> 0 < y
                        -> Rel r 0 x
                        -> r 0 (x * y)
                        -> r 0 x
solveMultPosRightZero pos r =
  |> rel r 0 (x * y)
  <> rel r (0 * y) (x * y) ~.. multZeroLeftAbsorbs
  <> rel r 0 x             ... solveMultPosRight pos

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling zero.
|||
||| ```idris example
||| |> 0 < x * y
||| <> x < 0     ... solveMultNegRightZero ylt0
||| ```
export
0 solveMultNegRightZero :  {x,y : Integer}
                        -> y < 0
                        -> Rel r x 0
                        -> r 0 (x * y)
                        -> r x 0
solveMultNegRightZero neg r =
  |> rel r 0 (x * y)
  <> rel r (0 * y) (x * y) ~.. multZeroLeftAbsorbs
  <> rel r x 0             ... solveMultNegRight neg

||| We can solve (in)equalities, with one side a multiplication
||| with a positive number and the other equalling zero.
|||
||| ```idris example
||| |> 0 < x * y
||| <> 0 < y     ... solveMultPosLeftZero xgt0
||| ```
export
0 solveMultPosLeftZero :  {x,y : Integer}
                        -> 0 < x
                        -> Rel r 0 y
                        -> r 0 (x * y)
                        -> r 0 y
solveMultPosLeftZero pos r =
  |> rel r 0 (x * y)
  <> rel r (x * 0) (x * y) ~.. multZeroRightAbsorbs
  <> rel r 0 y             ... solveMultPosLeft pos

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling zero.
|||
||| ```idris example
||| |> 0 < x * y
||| <> y < 0     ... solveMultNegLeftZero xlt0
||| ```
export
0 solveMultNegLeftZero :  {x,y : Integer}
                        -> x < 0
                        -> Rel r y 0
                        -> r 0 (x * y)
                        -> r y 0
solveMultNegLeftZero neg r =
  |> rel r 0 (x * y)
  <> rel r (x * 0) (x * y) ~.. multZeroRightAbsorbs
  <> rel r y 0             ... solveMultNegLeft neg

||| We can solve (in)equalities, with one side a multiplication
||| with a positive number and the other equalling the positive
||| number.
|||
||| ```idris example
||| |> y < x * y
||| <> 1 < x     ... solveMultPosRightSelf ygt0
||| ```
export
0 solveMultPosRightSelf :  {x,y : Integer}
                        -> 0 < y
                        -> Rel r 1 x
                        -> r y (x * y)
                        -> r 1 x
solveMultPosRightSelf pos r =
  |> rel r y (x * y)
  <> rel r (1 * y) (x * y) ~.. multOneLeftNeutral
  <> rel r 1 x             ... solveMultPosRight pos

||| We can solve (in)equalities, with one side a multiplication
||| with a positive number and the other equalling the positive
||| number.
|||
||| ```idris example
||| |> x < x * y
||| <> 1 < y     ... solveMultPosLeftSelf xgt0
||| ```
export
0 solveMultPosLeftSelf :  {x,y : Integer}
                       -> 0 < x
                       -> Rel r 1 y
                       -> r x (x * y)
                       -> r 1 y
solveMultPosLeftSelf pos r =
  |> rel r x (x * y)
  <> rel r (x * 1) (x * y) ~.. multOneRightNeutral
  <> rel r 1 y             ... solveMultPosLeft pos

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling the negative
||| number.
|||
||| ```idris example
||| |> y < x * y
||| <> x < 1     ... solveMultNegRightSelf ylt0
||| ```
export
0 solveMultNegRightSelf :  {x,y : Integer}
                        -> y < 0
                        -> Rel r x 1
                        -> r y (x * y)
                        -> r x 1
solveMultNegRightSelf neg r =
  |> rel r y (x * y)
  <> rel r (1 * y) (x * y) ~.. multOneLeftNeutral
  <> rel r x 1             ... solveMultNegRight neg

||| We can solve (in)equalities, with one side a multiplication
||| with a negative number and the other equalling the negative
||| number.
|||
||| ```idris example
||| |> x < x * y
||| <> y < 1     ... solveMultNegLeftSelf xlt0
||| ```
export
0 solveMultNegLeftSelf :  {x,y : Integer}
                        -> x < 0
                        -> Rel r y 1
                        -> r x (x * y)
                        -> r y 1
solveMultNegLeftSelf neg r =
  |> rel r x (x * y)
  <> rel r (x * 1) (x * y) ~.. multOneRightNeutral
  <> rel r y 1             ... solveMultNegLeft neg

--------------------------------------------------------------------------------
--          Division
--------------------------------------------------------------------------------

export
0 multDivP1 : {n,d : Integer} -> (0 < d) -> d * (div n d + 1) > n
multDivP1 dpos = App (snd $ modLT n d dpos) $
  |> mod n d               < d
  <> d * div n d + mod n d < d * div n d + d ... plusLeft
  <> n < d * (div n d + 1)                   =.= (
       lawDivMod n d %search
     , solve [n,d,div n d] (d .*. div n d +. d)
                           (d .* (div n d .+ 1))
     )

export
0 multDiv : {n,d : Integer} -> (0 < d) -> d * div n d <= n
multDiv dpos = App (fst $ modLT n d dpos) $
  |> 0 <= mod n d
  <> d * div n d + 0 <= d * div n d + mod n d ... plusLeft
  <> d * div n d     <= n                     =.= (
       plusZeroRightNeutral
     , lawDivMod n d %search
     )

export
0 divNonNeg : {n,d : Integer} -> (0 <= n) -> (0 < d) -> 0 <= div n d
divNonNeg ngte0 dpos = App (trans_GT_GTE (multDivP1 dpos) ngte0) $
  |> 0     <  d * (div n d + 1)
  <> 0     <  div n d + 1       ... solveMultPosLeftZero dpos
  <> 1     <= div n d + 1       ... (\_ => oneAfterZero _)
  <> 0     <= div n d           ... solvePlusRightSelf

export
0 modLTE : {n,d : Integer} -> (0 <= n) -> (0 < d) -> mod n d <= n
modLTE ngte0 dpos = App (divNonNeg ngte0 dpos) $
  |> 0               <= div n d
  <> d * 0           <= d * div n d           ... multPosLeft dpos
  <> d * 0 + mod n d <= d * div n d + mod n d ... plusRight
  <> mod n d         <= n                     =.= (
       solve [d, mod n d] (d .* 0 +. mod n d) (var (mod n d))
     , lawDivMod n d %search
     )

export
0 modOneIsZero : {n : Integer} -> mod n 1 === 0
modOneIsZero = assert_total $ case comp (mod n 1) 0 of
  EQ _ p _ => p
  LT p _ _ => void (LT_not_GTE p $ fst $ modLT n 1 %search)
  GT _ _ p => void (LT_not_GTE (snd $ modLT n 1 %search) (oneAfterZero _ p))

export
0 divOneSame : {n : Integer} -> div n 1 === n
divOneSame = assert_total $ Calc $
  |~ div n 1
  ~~ 1 * div n 1           ..< multOneLeftNeutral
  ~~ 1 * div n 1 + 0       ..< plusZeroRightNeutral
  ~~ 1 * div n 1 + mod n 1 ..< cong (1 * div n 1 +) modOneIsZero
  ~~ n                     ... lawDivMod n 1 %search

export
0 divGreaterOneLT : {n,d : Integer} -> 0 < n -> 1 < d -> div n d < n
divGreaterOneLT npos dgt1 =
  let dpos = the (0 < d) $ trans %search dgt1
   in assert_total $ case comp 0 (div n d) of
       EQ _ p _ => replace {p = (< n)} p npos
       LT p _ _ => App dgt1 $
         |> 1 < d
         <> 1 * div n d < d * div n d ... multPosRight p
         <> div n d     < d * div n d =.. multOneLeftNeutral
         <> div n d     < n           ... (\_ => trans_GTE_GT $ multDiv dpos)
       GT _ _ p => void (LT_not_GTE p $ divNonNeg %search dpos)
