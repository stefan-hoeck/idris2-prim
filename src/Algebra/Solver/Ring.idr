module Algebra.Solver.Ring

import public Algebra.Ring
import public Algebra.Solver.Prod
import public Algebra.Solver.Sum
import public Data.List.Elem
import Syntax.PreorderReasoning

%default total

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
eval : Neg a => Expr a as -> a
eval (Lit v)     = v
eval (Var x y)   = x
eval (Neg v)     = negate $ eval v
eval (Plus x y)  = eval x + eval y
eval (Mult x y)  = eval x * eval y
eval (Minus x y) = eval x - eval y

--------------------------------------------------------------------------------
--          Normalizer
--------------------------------------------------------------------------------

||| Normalizes an arithmetic expression to a sum of products.
public export
norm : Neg a => {as : List a} -> Expr a as -> Sum a as
norm (Lit n)     = [T n one]
norm (Var x y)   = [T 1 $ fromVar y]
norm (Neg x)     = negate $ norm x
norm (Plus x y)  = add (norm x) (norm y)
norm (Mult x y)  = mult (norm x) (norm y)
norm (Minus x y) = add (norm x) (negate $ norm y)

||| Like `norm` but removes all `zero` terms.
public export
normalize :
     {neg : _}
  -> SolvableNeg a neg
  => {as : List a}
  -> Expr a as
  -> Sum a as
normalize e = normSum (norm e)

--------------------------------------------------------------------------------
--          Proofs
--------------------------------------------------------------------------------

-- Evaluating an expression gives the same result as
-- evaluating its normalized form.
0 pnorm :
     {neg : _}
  -> Ring a neg
  => (e : Expr a as)
  -> eval e === esum (norm e)
pnorm (Lit n)    = Calc $
  |~ n
  ~~ n * 1                    ..< multOneRightNeutral
  ~~ n * eprod (one {as})     ..< cong (n *) (pone @{SRMultCMon} as)
  ~~ n * eprod (one {as}) + 0 ..< plusZeroRightNeutral

pnorm (Var x y)  = Calc $
  |~ x
  ~~ eprod (fromVar y)          ..< pvar @{SRMultCMon} as y
  ~~ 1 * eprod (fromVar y)      ..< multOneLeftNeutral
  ~~ 1 * eprod (fromVar y) + 0  ..< plusZeroRightNeutral

pnorm (Neg x) = Calc $
  |~ negate (eval x)
  ~~ negate (esum (norm x)) ... cong negate (pnorm x)
  ~~ esum (negate (norm x)) ..< pneg (norm x)

pnorm (Plus x y) = Calc $
  |~ eval x + eval y
  ~~ esum (norm x) + eval y
     ... cong (+ eval y) (pnorm x)
  ~~ esum (norm x) + esum (norm y)
     ... cong (esum (norm x) +) (pnorm y)
  ~~ esum (add (norm x) (norm y))
     ... padd _ _

pnorm (Mult x y) = Calc $
  |~ eval x * eval y
  ~~ esum (norm x) * eval y
     ... cong (* eval y) (pnorm x)
  ~~ esum (norm x) * esum (norm y)
     ... cong (esum (norm x) *) (pnorm y)
  ~~ esum (mult (norm x) (norm y))
     ... Sum.pmult _ _

pnorm (Minus x y) = Calc $
  |~ eval x - eval y
  ~~ eval x + negate (eval y)
     ... minusIsPlusNeg
  ~~ esum (norm x) + negate (eval y)
     ... cong (+ negate (eval y)) (pnorm x)
  ~~ esum (norm x) + negate (esum (norm y))
     ... cong (\v => esum (norm x) + negate v) (pnorm y)
  ~~ esum (norm x) + esum (negate (norm y))
     ..< cong (esum (norm x) +) (pneg (norm y))
  ~~ esum (add (norm x) (negate (norm y)))
     ... padd _ _

-- Evaluating an expression gives the same result as
-- evaluating its normalized form.
0 pnormalize :
     {neg : _}
  -> SolvableNeg a neg
  => Ring a neg
  => (e : Expr a as)
  -> eval e === esum (normalize e)
pnormalize e = Calc $
  |~ eval e
  ~~ esum (norm e)           ... pnorm e
  ~~ esum (normSum (norm e)) ..< pnormSum @{NegNum} @{RSR} (norm e)

--------------------------------------------------------------------------------
--          Solver
--------------------------------------------------------------------------------

||| Given a list `as` of variables and two arithmetic expressions
||| over these variables, if the expressions are converted
||| to the same normal form, evaluating them gives the same
||| result.
|||
||| This simple fact allows us to conveniently and quickly
||| proof arithmetic equalities required in other parts of
||| our code. For instance:
|||
||| ```idris example
||| 0 binom1 : {x,y : Bits8}
|||          -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
||| binom1 = solve [x,y]
|||                ((x .+. y) * (x .+. y))
|||                (x .*. x + 2 *. x *. y + y .*. y)
||| ```
export
0 solve :
     {neg : _}
  -> SolvableNeg a neg
  => Ring a neg
  => (as : List a)
  -> (e1,e2 : Expr a as)
  -> (prf : normalize e1 === normalize e2)
  => eval e1 === eval e2
solve _ e1 e2 = Calc $
  |~ eval e1
  ~~ esum (normalize e1) ...(pnormalize e1)
  ~~ esum (normalize e2) ...(cong esum prf)
  ~~ eval e2             ..<(pnormalize e2)

--------------------------------------------------------------------------------
--          Examples
--------------------------------------------------------------------------------

0 binom1 : {x,y : Bits8} -> (x + y) * (x + y) === x * x + 2 * x * y + y * y
binom1 = solve [x,y]
               ((x .+. y) * (x .+. y))
               (x .*. x + 2 *. x *. y + y .*. y)

0 binom2 : {x,y : Bits8} -> (x - y) * (x - y) === x * x - 2 * x * y + y * y
binom2 = solve [x,y]
               ((x .-. y) * (x .-. y))
               (x .*. x - 2 *. x *. y + y .*. y)

0 binom3 : {x,y : Bits8} -> (x + y) * (x - y) === x * x - y * y
binom3 = solve [x,y] ((x .+. y) * (x .-. y)) (x .*. x - y .*. y)
