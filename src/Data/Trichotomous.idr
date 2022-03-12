module Data.Trichotomous

||| Trichotomous formalises the fact that three relations are mutually
||| exclusive. It is meant to be used with relations that complement
||| each other so that the `Trichotomous lt eq gt` relation is the
||| total relation.
|||
||| All proofs held by a value of type `Trichotomous` are erased, so
||| at runtime such values get optimized to numbers 0, 1, or 2
||| respectively.
public export
data Trichotomous : (lt, eq, gt : a -> a -> Type) -> (a -> a -> Type) where
  MkLT :  {0 lt, eq, gt : a -> a -> Type}
       -> (0 _ : lt v w)
       -> (0 _ : Not (eq v w))
       -> (0 _ : Not (gt v w))
       -> Trichotomous lt eq gt v w

  MkEQ :  {0 lt, eq, gt : a -> a -> Type}
       -> (0 _ : Not (lt v w))
       -> (0 _ : eq v w)
       -> (0 _ : Not (gt v w))
       -> Trichotomous lt eq gt v w

  MkGT :  {0 lt, eq, gt : a -> a -> Type}
       -> (0 _ : Not (lt v w))
       -> (0 _ : Not (eq v w))
       -> (0 _ : gt v w)
       -> Trichotomous lt eq gt v w
