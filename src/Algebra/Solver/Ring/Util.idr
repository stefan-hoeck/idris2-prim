module Algebra.Solver.Ring.Util

import Algebra.Ring
import public Syntax.PreorderReasoning

%default total

export
0 p213 : RingLaws a => {k,m,n : a} -> k + (m + n) === m + (k + n)
p213 = Calc $
  |~ k + (m + n)
  ~~ (k + m) + n   ...(plusAssociative _ _ _)
  ~~ (m + k) + n   ...(cong (+n) $ plusCommutative _ _)
  ~~ m + (k + n)   ..<(plusAssociative _ _ _)

export
0 p1324 :  RingLaws a
        => {k,l,m,n : a}
        -> (k + l) + (m + n) === (k + m) + (l + n)
p1324 = Calc $
  |~ (k + l) + (m + n)
  ~~ ((k + l) + m) + n ...(plusAssociative _ _ _)
  ~~ (k + (l + m)) + n ..<(cong (+n) $ plusAssociative _ _ _)
  ~~ (k + (m + l)) + n ...(cong (\x => (k + x) + n) $ plusCommutative _ _)
  ~~ ((k + m) + l) + n ...(cong (+n) $ plusAssociative _ _ _)
  ~~ (k + m) + (l + n) ..<(plusAssociative _ _ _)

export
0 m1324 :  RingLaws a
        => {k,l,m,n : a}
        -> (k * l) * (m * n) === (k * m) * (l * n)
m1324 = Calc $
  |~ (k * l) * (m * n)
  ~~ ((k * l) * m) * n ...(multAssociative _ _ _)
  ~~ (k * (l * m)) * n ..<(cong (*n) $ multAssociative _ _ _)
  ~~ (k * (m * l)) * n ...(cong (\x => (k * x) * n) $ multCommutative _ _)
  ~~ ((k * m) * l) * n ...(cong (*n) $ multAssociative _ _ _)
  ~~ (k * m) * (l * n) ..<(multAssociative _ _ _)
