module Char

import Data.Prim.Char
import Data.SOP
import Hedgehog

allChar : Gen Char
allChar = unicodeAll

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allChar
  (b8 >= MinChar) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allChar, allChar]
  toOrdering (comp m n) === compare m n

export
props : Group
props =
  MkGroup
    "Char"
    [ ("prop_ltMin",  prop_ltMin)
    , ("prop_comp",   prop_comp)
    ]
