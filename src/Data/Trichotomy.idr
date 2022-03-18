module Data.Trichotomy

%default total

||| Trichotomy formalises the fact that three relations are mutually
||| exclusive. A value of type `Trichotomy lt m n` proofs, that
||| exactly one of the relations `lt m n`, `m === n`, or `lt n m` holds.
|||
||| All proofs held by a value of type `Trichotomous` are erased, so
||| at runtime such values get optimized to numbers 0, 1, or 2
||| respectively.
public export
data Trichotomy : (lt : a -> a -> Type) -> (a -> a -> Type) where
  LT :  {0 lt : a -> a -> Type}
     -> (0 _ : lt v w)
     -> (0 _ : Not (v === w))
     -> (0 _ : Not (lt w v))
     -> Trichotomy lt v w

  EQ :  {0 lt : a -> a -> Type}
     -> (0 _ : Not (lt v w))
     -> (0 _ : v === w)
     -> (0 _ : Not (lt w v))
     -> Trichotomy lt v w

  GT :  {0 lt : a -> a -> Type}
     -> (0 _ : Not (lt v w))
     -> (0 _ : Not (v === w))
     -> (0 _ : lt w v)
     -> Trichotomy lt v w

public export
Eq (Trichotomy lt m n) where
  LT _ _ _ == LT _ _ _ = True
  EQ _ _ _ == EQ _ _ _ = True
  GT _ _ _ == GT _ _ _ = True
  _        == _        = False

public export
Ord (Trichotomy lt m n) where
  compare (LT _ _ _) (LT _ _ _) = EQ
  compare (LT _ _ _) _          = LT
  compare _          (LT _ _ _) = GT
  compare (EQ _ _ _) (EQ _ _ _) = EQ
  compare (EQ _ _ _) _          = LT
  compare _          (EQ _ _ _) = GT
  compare (GT _ _ _) (GT _ _ _) = EQ

public export
Show (Trichotomy lt m n) where
  show (LT _ _ _) = "LT"
  show (EQ _ _ _) = "EQ"
  show (GT _ _ _) = "GT"

public export
toOrdering : Trichotomy lt m n -> Ordering
toOrdering (LT _ _ _) = LT
toOrdering (EQ _ _ _) = EQ
toOrdering (GT _ _ _) = GT
