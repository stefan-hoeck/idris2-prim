module RingLaws

import public Algebra.Ring
import Data.SOP
import Hedgehog

prop_plusCommutative : Show a => Eq a => Ring a => Gen a -> Property
prop_plusCommutative g = property $ do
  [m,n] <- forAll $ np [g,g]
  m + n === n + m

prop_plusAssociative : Show a => Eq a => Ring a => Gen a -> Property
prop_plusAssociative g = property $ do
  [k,m,n] <- forAll $ np [g,g,g]
  k + (m + n) === k + (n + m)

prop_plusZeroLeftNeutral : Show a => Eq a => Ring a => Gen a -> Property
prop_plusZeroLeftNeutral g = property $ do
  n <- forAll g
  0 + n === n

prop_plusNegateLeftZero : Show a => Eq a => Ring a => Gen a -> Property
prop_plusNegateLeftZero g = property $ do
  n <- forAll g
  negate n + n === 0

prop_multCommutative : Show a => Eq a => Ring a => Gen a -> Property
prop_multCommutative g = property $ do
  [m,n] <- forAll $ np [g,g]
  m * n === n * m

prop_multAssociative : Show a => Eq a => Ring a => Gen a -> Property
prop_multAssociative g = property $ do
  [k,m,n] <- forAll $ np [g,g,g]
  k * (m * n) === k * (n * m)

prop_multOneLeftNeutral : Show a => Eq a => Ring a => Gen a -> Property
prop_multOneLeftNeutral g = property $ do
  n <- forAll g
  1 * n === n

prop_distributive : Show a => Eq a => Ring a => Gen a -> Property
prop_distributive g = property $ do
  [k,m,n] <- forAll $ np [g,g,g]
  k * (m + n) === (k * m) + (k * n)

prop_minusIsPlusNegate : Show a => Eq a => Ring a => Gen a -> Property
prop_minusIsPlusNegate g = property $ do
  [m,n] <- forAll $ np [g,g]
  m - n === m + negate n

export
ringProps :  Show a
          => Eq a
          => Ring a
          => Gen a
          -> List (PropertyName,Property)
ringProps g =
  [ ("prop_plusCommutative",     prop_plusCommutative g)
  , ("prop_plusAssociative",     prop_plusAssociative g)
  , ("prop_plusZeroLeftNeutral", prop_plusZeroLeftNeutral g)
  , ("prop_plusNegateLeftZero",  prop_plusNegateLeftZero g)
  , ("prop_multCommutative",     prop_multCommutative g)
  , ("prop_multAssociative",     prop_multAssociative g)
  , ("prop_multOneLeftNeutral",  prop_multOneLeftNeutral g)
  , ("prop_distributive",        prop_distributive g)
  , ("prop_minusIsPlusNegate",   prop_minusIsPlusNegate g)
  ]
