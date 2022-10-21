||| This module provides syntax for deriving inequalities similar
||| to the one available from `Syntax.PreorderReasoning`
||| and `Syntax.PreorderReasoning.Generic` from the base library.
module Syntax.Total

import public Data.Prim.Ord
import public Syntax.PreorderReasoning

%default total

prefix 1  |~
infixl 0  ~~
infixl 0  <~
infix  1  ...,.~.,.<.,.=.

||| A single step in deducing a transitive chain of inequalities.
|||
||| Additional smart constructors are `(.=.)`, `(.<.)`, and `(.~.)`.
data Step : (lt : a -> a -> Type) -> (x,y : a) -> Type where
  (...) : (0 y : a) -> (0 prf : LTE lt x y) -> Step lt x y

||| A transitive chain of inequalities.
|||
||| We can derive a value of type `LTE lt x y` from a value of
||| type `FastDerivation lt x y` by using `CalcLTE`. If we can verify (via `HasLT`),
||| that at least of the deduction steps is strict, we can even use `CalcLT` to
||| derive a value of type `lt x y`.
public export
data FastDerivation : (lt : a -> a -> Type) -> (x : a) -> (y : a) -> Type where
  (|~) : (x : a) -> FastDerivation lt x x
  (<~) : {x, y : a}
         -> FastDerivation lt x y -> {z : a} -> (step : Step lt y z)
         -> FastDerivation lt x z

||| Proof that a `FastDerivation` constains at list one strict
||| inequality.
data HasLT : (stps : FastDerivation lt x y) -> Type where
  Here  : HasLT (stps <~ _ ... Left p)
  There : HasLT stps -> HasLT (stps <~ stp)

||| Convenience alias for `(...)` to be used with a proof of equality.
public export
0 (.=.) : (0 y : a) -> (0 prf : x === y) -> Step lt x y
y .=. prf = y ... Right prf

||| Convenience alias for `(...)` to be used with a proof of equality
||| with the arguments switched.
public export
0 (.~.) : (0 y : a) -> (0 prf : y === x) -> Step lt x y
y .~. prf = y .=. sym prf

||| Convenience alias for `(...)` to be used with a proof of strict
||| inequality (`x` is strictly less than `y`).
public export
0 (.<.) : (0 y : a) -> (0 prf : lt x y) -> Step lt x y
y .<. prf = y ... Left prf

||| Given a total order `lt`, we can use this to derive a `LTE lt x y`
||| from a transitive chain (of type `FastDerivation lt x y`) of
||| inequalities.
public export
0 CalcLTE :
     Total a lt
  => FastDerivation lt x y
  -> LTE lt x y
CalcLTE (|~ _)               = Right Refl
CalcLTE (stps <~ _  ... prf) = trans (CalcLTE stps) prf

||| Like `CalcLT` but for deriving string inequalities. In order
||| to do so, at least one inequality in the `FastDerivation lt x y`
||| must be strict (as witnessed by the proof of type `HasLT`).
public export
0 CalcLT :
     {lt : a -> a -> Type}
  -> Total a lt
  => (stps : FastDerivation lt x y)
  -> (0 p  : HasLT stps)
  => lt x y
CalcLT (stps <~ _ ... Left x) {p = Here}    = trans_LTE_LT (CalcLTE stps) x
CalcLT (stps <~ _ ... x)      {p = There q} = trans_LT_LTE (CalcLT stps) x
