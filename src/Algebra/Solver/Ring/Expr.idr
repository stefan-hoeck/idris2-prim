module Algebra.Solver.Ring.Expr

import public Data.List.Elem
import public Algebra.Ring
import Syntax.PreorderReasoning

%default total

--------------------------------------------------------------------------------
--          Natural Numbers
--------------------------------------------------------------------------------

||| Multiplies a value `n` times with itself. In case of `n`
||| being zero, this returns `1`.
public export
pow : Ring a => a -> Nat -> a
pow x 0     = 1
pow x (S k) = x * pow x k

--------------------------------------------------------------------------------
--          Expression
--------------------------------------------------------------------------------

||| Data type representing expressions in a commutative ring.
|||
||| This is used to at compile time compare different forms of
||| the same expression and proof that they evaluate to
||| the same result.
|||
||| An example:
|||
||| ```idris example
||| 0 binom1 : {x,y : Bits8} -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
||| binom1 = solve [x,y]
|||                ((x .+. y) * (x .+. y))
|||                (x .*. x + 2 *. x *. y + y .*. y)
||| ```
|||
||| @ a  the type used in the arithmetic expression
||| @ as list of variables which don't reduce at compile time
|||
||| In the example above, `x` and `y` are variables, while `2`
||| is a literal known at compile time. To make working with
||| variables more convenient (the have to be wrapped in data
||| constructor `Var`, by using function `var` for instance),
||| additional operators for addition, multiplication, and
||| subtraction are provided.
|||
||| In order to proof that two expressions evaluate to the
||| same results, the following steps are taken at compile
||| time:
|||
||| 1. Both expressions are converted to a normal form via
|||    `Algebra.Solver.Ring.Sum.normalize`.
||| 2. The normal forms are compared for being identical.
||| 3. Since in `Algebra.Solver.Ring.Sum` there is a proof that
|||    converting an expression to its normal form does not
|||    affect the result when evaluating it, if the normal
|||    forms are identical, the two expressions must evaluate
|||    to the same result.
|||
||| You can find several examples of making use of this
||| in `Data.Prim.Integer.Extra`.
public export
data Expr : (a : Type) -> (as : List a) -> Type where
  Lit   : (v : a) -> Expr a as
  Var   : (x : a) -> Elem x as -> Expr a as
  Neg   : Expr a as -> Expr a as
  Plus  : (x,y : Expr a as) -> Expr a as
  Mult  : (x,y : Expr a as) -> Expr a as
  Minus : (x,y : Expr a as) -> Expr a as

public export
Num a => Num (Expr a as) where
  (+) = Plus
  (*) = Mult
  fromInteger = Lit . fromInteger

public export
Neg a => Neg (Expr a as) where
  negate = Neg
  (-)    = Minus

public export
var : {0 as : List a} -> (x : a) -> Elem x as => Expr a as
var x = Var x %search

--------------------------------------------------------------------------------
--          Syntax
--------------------------------------------------------------------------------

infixl 8 .+., .+, +.

infixl 8 .-., .-, -.

infixl 9 .*., .*, *.

public export
(.+.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.+.) x y = Plus (var x) (var y)

public export
(+.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(+.) x y = Plus x (var y)

public export
(.+) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.+) x y = Plus (var x) y

public export
(.-.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.-.) x y = Minus (var x) (var y)

public export
(-.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(-.) x y = Minus x (var y)

public export
(.-) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.-) x y = Minus (var x) y

public export
(.*.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.*.) x y = Mult (var x) (var y)

public export
(*.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(*.) x y = Mult x (var y)

public export
(.*) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.*) x y = Mult (var x) y

--------------------------------------------------------------------------------
--          Evaluation
--------------------------------------------------------------------------------

public export
eval : Ring a => Expr a as -> a
eval (Lit v)     = v
eval (Var x y)   = x
eval (Neg v)     = neg $ eval v
eval (Plus x y)  = eval x + eval y
eval (Mult x y)  = eval x * eval y
eval (Minus x y) = eval x - eval y

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

export
0 ppow : Ring a
       => (m,n : Nat)
       -> (x   : a)
       -> pow x (m + n) === pow x m * pow x n
ppow 0     n x = sym multOneLeftNeutral
ppow (S k) n x = Calc $
  |~ x * pow x (plus k n)
  ~~ x * (pow x k * pow x n) ... cong (x*) (ppow k n x)
  ~~ (x * pow x k) * pow x n ... multAssociative
