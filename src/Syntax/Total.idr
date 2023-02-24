||| This module provides syntax for deriving inequalities similar
||| to the one available from `Syntax.PreorderReasoning`
||| and `Syntax.PreorderReasoning.Generic` from the base library.
module Syntax.Total

import public Data.Prim.Ord
import public Syntax.PreorderReasoning

%default total

prefix 1  |~
infixl 0  <~,<!
infix  1  ...,.~.,.<.,.=.

public export
data Rel : (strict : Bool) -> (a -> a -> Type) -> a -> a -> Type where
  LT : {lt : a -> a -> Type} -> lt x y -> Rel b lt x y
  EQ : {lt : a -> a -> Type} -> x === y -> Rel False lt x y

export
0 transL : Total a lt => Rel b1 lt x y -> Rel b2 lt y z -> Rel b1 lt x z
transL (LT p1) (LT p2) = LT $ trans p1 p2
transL (LT p1) (EQ p2) = LT $ trans_LT_EQ p1 p2
transL (EQ p1) (LT p2) = LT $ trans_EQ_LT p1 p2
transL (EQ p1) (EQ p2) = EQ $ trans p1 p2

export
0 transR : Total a lt => Rel b1 lt x y -> Rel b2 lt y z -> Rel b2 lt x z
transR (LT p1) (LT p2) = LT $ trans p1 p2
transR (LT p1) (EQ p2) = LT $ trans_LT_EQ p1 p2
transR (EQ p1) (LT p2) = LT $ trans_EQ_LT p1 p2
transR (EQ p1) (EQ p2) = EQ $ trans p1 p2

export
0 toLTE : Rel b lt x y -> LTE lt x y
toLTE (LT p) = Left p
toLTE (EQ p) = Right p

export
0 toLT : Rel True lt x y -> lt x y
toLT (LT p) = p
toLT (EQ p) impossible

||| A single step in deducing a transitive chain of inequalities.
|||
||| Additional smart constructors are `(.=.)`, `(.<.)`, and `(.~.)`.
public export
data Step : (str : Bool) -> (lt : a -> a -> Type) -> (x,y : a) -> Type where
  (...) : (0 y : a) -> (0 prf : Rel str lt x y) -> Step str lt x y

||| A transitive chain of inequalities.
|||
||| We can derive a value of type `LTE lt x y` from a value of
||| type `FastDerivation lt x y` by using `CalcLTE`. If we can verify (via `HasLT`),
||| that at least of the deduction steps is strict, we can even use `CalcLT` to
||| derive a value of type `lt x y`.
public export
data FastDerivation :  (strict : Bool)
                    -> (lt : a -> a -> Type)
                    -> (x : a)
                    -> (y : a)
                    -> Type where
  (|~) : (x : a) -> FastDerivation False lt x x

  (<~) :  FastDerivation b lt x y
       -> (step : Step c lt y z)
       -> FastDerivation b lt x z

  (<!) :  FastDerivation b lt x y
       -> (step : Step c lt y z)
       -> FastDerivation c lt x z

||| Convenience alias for `(...)` to be used with a proof of equality.
public export
0 (.=.) : (0 y : a) -> (0 prf : x === y) -> Step False lt x y
y .=. prf = y ... EQ prf

||| Convenience alias for `(...)` to be used with a proof of equality
||| with the arguments switched.
public export
0 (.~.) : (0 y : a) -> (0 prf : y === x) -> Step False lt x y
y .~. prf = y .=. sym prf

||| Convenience alias for `(...)` to be used with a proof of strict
||| inequality (`x` is strictly less than `y`).
public export
0 (.<.) : (0 y : a) -> (0 prf : lt x y) -> Step True lt x y
y .<. prf = y ... LT prf

||| Given a total order `lt`, we can use this to derive a `LTE lt x y`
||| from a transitive chain (of type `FastDerivation lt x y`) of
||| inequalities.
export
0 CalcLTE :
     Total a lt
  => FastDerivation b lt x z
  -> LTE lt x z
CalcLTE (|~ _)            = Right Refl
CalcLTE (stps <~ _ ... stp) = trans (CalcLTE stps) (toLTE stp)
CalcLTE (stps <! _ ... stp) = trans (CalcLTE stps) (toLTE stp)

||| Like `CalcLT` but for deriving strict inequalities.
public export
0 CalcLT :
     {lt : a -> a -> Type}
  -> Total a lt
  => (stps : FastDerivation True lt x y)
  -> lt x y
CalcLT (stps <~ _ ... stp) = trans_LT_LTE (CalcLT  stps) (toLTE stp)
CalcLT (stps <! _ ... stp) = trans_LTE_LT (CalcLTE stps) (toLT stp)

export
0 CalcAny :
     Total a lt
  => FastDerivation b lt x z
  -> Rel b lt x z
CalcAny (|~ x)           = EQ Refl
CalcAny (y <~ _ ... stp) = transL (CalcAny y) stp
CalcAny (y <! _ ... stp) = transR (CalcAny y) stp

