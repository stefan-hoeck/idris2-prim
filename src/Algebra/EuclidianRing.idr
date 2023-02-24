module Algebra.EuclidianRing

import Data.Nat
import public Algebra.Ring
import public Syntax.PreorderReasoning

%default total

public export
interface Neg a => Integral a => ERing a where

public export %inline
rngNeg : ERing a -> Neg a
rngNeg _ = %search

public export
interface EuclidianRing a (0 rng : ERing a) | a where
  constructor MkEuclidianRing
  norm : a -> Nat

  0 err : Ring a (rngNeg rng)

  0 divMod :
       {n,d : a}
    -> Not (d === 0)
    -> d * div n d + mod n d === n

  0 modNegEQ :
       {n,d : a}
    -> Not (d === 0)
    -> mod n d === mod n (negate d)

  0 zeroNotOne : Not (the a 0 === the a 1)

  0 modLT :
       {n,d : a}
    -> Not (d === 0)
    -> norm (mod n d) `LT` norm d

public export %inline %hint
0 ERR : EuclidianRing a rng => Ring a (rngNeg rng)
ERR = err

public export %inline %hint
0 ERSR : EuclidianRing a rng => Semiring a (negNum $ rngNeg rng)
ERSR = RSR @{ERR}

--------------------------------------------------------------------------------
--          Division Lemmata
--------------------------------------------------------------------------------

export
0 oneNotZero :
     {rng : _}
  -> EuclidianRing a rng
  => Not (the a 1 === the a 0)
oneNotZero p = zeroNotOne $ sym p

||| Is this an axiom or a lemma
export
0 divLeft :
     {rng : _}
  -> EuclidianRing a rng
  => {n,d : a}
  -> Not (d === 0)
  -> div (d * n) d === n

export
0 divRight :
     {rng : _}
  -> EuclidianRing a rng
  => {n,d : a}
  -> Not (d === 0)
  -> div (n * d) d === n
divRight p = Calc $
  |~ div (n * d) d
  ~~ div (d * n) d ... cong (`div` d) (multCommutative @{ERSR})
  ~~ n             ... divLeft p

export
0 divZero :
     {rng : _}
  -> EuclidianRing a rng
  => {n,d : a}
  -> Not (d === 0)
  -> div 0 d === 0
divZero p = Calc $
  |~ div 0 d
  ~~ div (d * 0) d ..< cong (`div` d) (multZeroRightAbsorbs @{ERSR})
  ~~ 0             ... divLeft p

export
0 divByOneNeutral :
     {rng : _}
  -> EuclidianRing a rng
  => {n : a}
  -> div n 1 === n
divByOneNeutral = Calc $
  |~ div n 1
  ~~ div (1 * n) 1 ..< cong (`div` 1) (multOneLeftNeutral @{ERSR})
  ~~ n             ... divLeft oneNotZero
