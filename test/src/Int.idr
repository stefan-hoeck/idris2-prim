module Int

import Data.Prim.Int
import Data.SOP
import Hedgehog
import RingLaws

allInt : Gen Int
allInt = int (linear (-0x8000000000000000) 0xffffffffffffffff)

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allInt, allInt]
  toOrdering (comp m n) === compare m n

export
props : Group
props =
  MkGroup "Int16" $
    [ ("prop_comp",   prop_comp)
    ] ++ ringProps allInt
