module Test.Int8

import Data.Prim.Int8
import Data.SOP
import Hedgehog

allInt8 : Gen Int8
allInt8 = int8 (linear (-0x80) 0xff)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allInt8
  (b8 <= MaxInt8) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allInt8
  (b8 >= MinInt8) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInt8, allInt8]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int8"
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ]
