module String

import Data.Prim.String
import Data.SOP
import Hedgehog

allString : Gen String
allString = string (linear 0 30) unicodeAll

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allString
  (b8 >= MinString) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allString, allString]
  toOrdering (comp m n) === compare m n

export
props : Group
props = MkGroup "String"
  [ ("prop_ltMin",  prop_ltMin)
  , ("prop_comp",   prop_comp)
  ]

