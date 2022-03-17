module Test.Int16

import Data.Prim.Int16
import Data.SOP
import Hedgehog
import Test.RingLaws

allInt16 : Gen Int16
allInt16 = int16 (linear (-0x8000) 0xffff)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allInt16
  (b8 <= MaxInt16) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allInt16
  (b8 >= MinInt16) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInt16, allInt16]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int16" $
  [ ("prop_ltMax",  prop_ltMax)
  , ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ] ++ ringProps allInt16
