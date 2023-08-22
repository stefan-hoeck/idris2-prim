module Algebra.Solver.Ring.Util

import Algebra.Ring
import public Syntax.PreorderReasoning

%default total

export
0 p213 : Ring a => {k,m,n : a} -> k + (m + n) === m + (k + n)
p213 = Calc $
  |~ k + (m + n)
  ~~ (k + m) + n   ... plusAssociative
  ~~ (m + k) + n   ... cong (+n) plusCommutative
  ~~ m + (k + n)   ..< plusAssociative

export
0 p1324 :
     {auto _ : Ring a}
  -> {k,l,m,n : a}
  -> (k + l) + (m + n) === (k + m) + (l + n)
p1324 = Calc $
  |~ (k + l) + (m + n)
  ~~ ((k + l) + m) + n ... plusAssociative
  ~~ (k + (l + m)) + n ..< cong (+n) plusAssociative
  ~~ (k + (m + l)) + n ... cong (\x => (k + x) + n) plusCommutative
  ~~ ((k + m) + l) + n ... cong (+n) plusAssociative
  ~~ (k + m) + (l + n) ..< plusAssociative

export
0 m1324 :
     {auto _ : Ring a}
  -> {k,l,m,n : a}
  -> (k * l) * (m * n) === (k * m) * (l * n)
m1324 = Calc $
  |~ (k * l) * (m * n)
  ~~ ((k * l) * m) * n ... multAssociative
  ~~ (k * (l * m)) * n ..< cong (*n) multAssociative
  ~~ (k * (m * l)) * n ... cong (\x => (k * x) * n) multCommutative
  ~~ ((k * m) * l) * n ... cong (*n) multAssociative
  ~~ (k * m) * (l * n) ..< multAssociative
