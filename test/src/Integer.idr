module Integer

import Data.Prim.Integer
import Data.SOP
import Hedgehog
import RingLaws

allInteger : Gen Integer
allInteger = integer (linear (-0x8000000000000000) 0xffffffffffffffff)

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInteger, allInteger]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "Int16" $
  [ ("prop_comp",   prop_comp)
  ] ++ ringProps allInteger
