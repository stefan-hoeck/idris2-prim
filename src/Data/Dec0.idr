module Data.Dec0

%default total

||| Erased decidability.
|||
||| This is just like `Dec`, but with erased proofs.
|||
||| At runtime, the two constructors are optimized
||| to constants 0 or 1, respectively.
public export
data Dec0 : (prop : Type) -> Type where
  Yes0 : (0 p : prop) -> Dec0 prop
  No0  : (0 contra : prop -> Void) -> Dec0 prop

||| Witness that a value of type `Dec0 prop` is actually a `Yes0`.
public export
data IsYes0 : (d : Dec0 prop) -> Type where
  ItIsYes0 : {0 prf : _} -> IsYes0 (Yes0 prf)

||| Witness that a value of type `Dec0 prop` is actually a `No0`.
public export
data IsNo0 : (d : Dec0 prop) -> Type where
  ItIsNo0 : {0 contra : _} -> IsNo0 (No0 contra)

||| Safely extract a proposition from a `Dec0`.
public export
0 fromYes0 : (d : Dec0 prop) -> {auto 0 _ : IsYes0 d} -> prop
fromYes0 (Yes0 p) = p
fromYes0 (No0 _) impossible

||| Safely extract a proof of contradiction from a `No0`.
public export
0 fromNo0 : (d : Dec0 prop) -> {auto 0 _ : IsNo0 d} -> Not prop
fromNo0 (No0 p) = p
fromNo0 (Yes0 _) impossible

||| Decidably test if a boolean value is `True`.
public export
test : (b : Bool) -> Dec0 (b === True)
test True  = Yes0 Refl
test False = No0 absurd
