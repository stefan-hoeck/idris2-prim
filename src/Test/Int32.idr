module Test.Int32

import Data.Prim.Int32
import Data.SOP
import Hedgehog
import Test.RingLaws

allInt32 : Gen Int32
allInt32 = int32 (linear (-0x80000000) 0xffffffff)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allInt32
  (b8 <= MaxInt32) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allInt32
  (b8 >= MinInt32) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInt32, allInt32]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int32" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ] ++ ringProps allInt32
