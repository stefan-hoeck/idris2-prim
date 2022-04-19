module Data.Maybe.NothingMin

import Control.Function
import Data.Maybe
import Data.Prim.Ord

%default total

||| A total order for `Maybe a` where `a` has a total order
||| and `Nothing` is the minimal value.
|||
||| This is useful, for instance, when implementing provably
||| sorted snoc-lists, indexed by a `Maybe key`, where
||| the empty snoc-list has a `Nothing` index:
|||
||| ```idris example
||| data AssocSnocList : (ix : Maybe Bits8) -> (a : Type) -> Type where
|||   Lin  : AssocSnocList Nothing a
|||   (:<) :  (ps : AssocSnocList ix a)
|||        -> (p : (Bits8, a))
|||        -> (0 prf : LT (<) ix (Just $ fst p))
|||        => AssocSnocList (Just $ fst p) a
||| ```
public export
data LT : (lt : a -> a -> Type) -> (m1,m2 : Maybe a) -> Type where
  LTNothing : LT lt Nothing (Just v)
  LTJust    :  {0 lt : a -> a -> Type}
            -> {0 v, w : a}
            -> lt v w -> LT lt (Just v) (Just w)

public export
Uninhabited (LT lt m Nothing) where
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
comp Nothing (Just x)  = LT LTNothing absurd absurd
comp (Just y) Nothing  = GT absurd absurd LTNothing
comp Nothing  Nothing  = EQ absurd Refl absurd

||| If `lt` is a total order of `a`, then `LT lt` is a
||| total order of `Maybe a`.
export %inline
Total a lt => Total (Maybe a) (LT lt) where
  trichotomy = comp

  transLT LTNothing  (LTJust y) = LTNothing
  transLT (LTJust x) (LTJust y) = LTJust $ trans x y
  transLT y          LTNothing  = absurd y
