module Test.Int64

import Data.Prim.Int64
import Data.SOP
import Hedgehog

allInt64 : Gen Int64
allInt64 = int64 (linear (-0x8000000000000000) 0xffffffffffffffff)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allInt64
  (b8 <= MaxInt64) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allInt64
  (b8 >= MinInt64) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInt64, allInt64]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int64"
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ]
