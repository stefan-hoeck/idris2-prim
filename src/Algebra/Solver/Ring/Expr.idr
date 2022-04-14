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
  ||| A literal. This should be a value known at compile time
  ||| so that it reduces during normalization.
  Lit   : (v : a) -> Expr a as

  ||| A variabl. This is is for values not known at compile
  ||| time. In order to compare and merge variables, we need an
  ||| `Elem x as` proof.
  Var   : (x : a) -> Elem x as -> Expr a as

  ||| Negates and expression.
  Neg   : Expr a as -> Expr a as

  ||| Addition of two expressions.
  Plus  : (x,y : Expr a as) -> Expr a as

  ||| Multiplication of two expressions.
  Mult  : (x,y : Expr a as) -> Expr a as

  ||| Subtraction of two expressions.
  Minus : (x,y : Expr a as) -> Expr a as

||| While this allows you to use the usual operators
||| for addition and multiplication, it is often convenient
||| to use related operators `.*.`, `.+.`, and similar when
||| working with variables.
public export
Num a => Num (Expr a as) where
  (+) = Plus
  (*) = Mult
  fromInteger = Lit . fromInteger

public export
Neg a => Neg (Expr a as) where
  negate = Neg
  (-)    = Minus

||| Like `Var` but takes the `Elem x as` as an auto implicit
||| argument.
public export
var : {0 as : List a} -> (x : a) -> Elem x as => Expr a as
var x = Var x %search

--------------------------------------------------------------------------------
--          Syntax
--------------------------------------------------------------------------------

infixl 8 .+., .+, +.

infixl 8 .-., .-, -.

infixl 9 .*., .*, *.

||| Addition of variables. This is an alias for
||| `var x + var y`.
public export
(.+.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.+.) x y = Plus (var x) (var y)

||| Addition of variables. This is an alias for
||| `x + var y`.
public export
(+.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(+.) x y = Plus x (var y)

||| Addition of variables. This is an alias for
||| `var x + y`.
public export
(.+) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.+) x y = Plus (var x) y

||| Subtraction of variables. This is an alias for
||| `var x - var y`.
public export
(.-.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.-.) x y = Minus (var x) (var y)

||| Subtraction of variables. This is an alias for
||| `x - var y`.
public export
(-.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(-.) x y = Minus x (var y)

||| Subtraction of variables. This is an alias for
||| `var x - y`.
public export
(.-) :  {0 as : List a}
     -> (x : a)
     -> (y : Expr a as)
     -> Elem x as
     => Expr a as
(.-) x y = Minus (var x) y

||| Multiplication of variables. This is an alias for
||| `var x * var y`.
public export
(.*.) :  {0 as : List a}
      -> (x,y : a)
      -> Elem x as
      => Elem y as
      => Expr a as
(.*.) x y = Mult (var x) (var y)

||| Multiplication of variables. This is an alias for
||| `var x * y`.
public export
(*.) :  {0 as : List a}
     -> (x : Expr a as)
     -> (y : a)
     -> Elem y as
     => Expr a as
(*.) x y = Mult x (var y)

||| Multiplication of variables. This is an alias for
||| `x * var y`.
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

||| Evaluation of expressions. This keeps the exact
||| structure of the expression tree. For instance
||| `eval $ x .*. (y .+. z)` evaluates to `x * (y + z)`.
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

||| Proof that addition of exponents is equivalent to multiplcation
||| of the two terms.
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
