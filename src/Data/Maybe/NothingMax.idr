module Data.Maybe.NothingMax

import Control.Function
import Data.Maybe
import Data.Prim.Ord

%default total

||| A total order for `Maybe a` where `a` has a total order
||| and `Nothing` is the maximal value.
|||
||| This is useful, for instance, when implementing provably
||| sorted (assoc-) lists, indexed by a `Maybe key`, where
||| the empty list has a `Nothing` index:
|||
||| ```idris example
||| data AssocList : (ix : Maybe Bits8) -> (a : Type) -> Type where
|||   Nil  : AssocList Nothing a
|||   (::) :  (p : (Bits8, a))
|||        -> (ps : AssocList ix a)
|||        -> (0 prf : LT (<) (Just $ fst p) ix)
|||        => AssocList (Just $ fst p) a
||| ```
public export
data LT : (lt : a -> a -> Type) -> (m1,m2 : Maybe a) -> Type where
  LTNothing : LT lt (Just v) Nothing
  LTJust    :  {0 lt : a -> a -> Type}
            -> {0 v, w : a}
            -> lt v w -> LT lt (Just v) (Just w)

public export
Uninhabited (LT lt Nothing m) where
  uninhabited LTNothing impossible
  uninhabited (LTJust _) impossible

public export
Total a lt => Uninhabited (LT lt (Just k) (Just k)) where
  uninhabited LTNothing impossible
  uninhabited (LTJust refl) = void (irrefl refl)

public export
fromLT : LT lt (Just a) (Just b) -> lt a b
fromLT (LTJust x) = x

||| Implementation and alias for `trichotomy`.
export
comp : Total a lt => (m1,m2 : Maybe a) -> Trichotomy (LT lt) m1 m2
comp (Just x) (Just y) = case trichotomy {lt} x y of
  LT p c1 c2 => LT (LTJust p) (\r => c1 (injective r)) (\x => c2 (fromLT x))
  EQ c1 p c2 => EQ (\x => c1 (fromLT x)) (cong Just p) (\x => c2 (fromLT x))
  GT c1 c2 p => GT (\x => c1 (fromLT x)) (\r => c2 (injective r)) (LTJust p)
comp (Just x) Nothing  = LT LTNothing absurd absurd
comp Nothing  (Just y) = GT absurd absurd LTNothing
comp Nothing  Nothing  = EQ absurd Refl absurd

||| If `lt` is a total order of `a`, then `LT lt` is a
||| total order of `Maybe a`.
export %inline
Total a lt => Total (Maybe a) (LT lt) where
  trichotomy = comp

  transLT (LTJust x) LTNothing  = LTNothing
  transLT (LTJust x) (LTJust y) = LTJust $ trans x y
  transLT LTNothing  y          = absurd y
