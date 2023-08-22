module Bits32

import Data.Prim.Bits32
import Data.SOP
import Hedgehog
import RingLaws

allBits32 : Gen Bits32
allBits32 = bits32 (linear 0 0xffffffff)

gt0 : Gen Bits32
gt0 = bits32 (linear 1 MaxBits32)

gt1 : Gen Bits32
gt1 = bits32 (linear 2 MaxBits32)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allBits32
  (b8 <= MaxBits32) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allBits32
  (b8 >= MinBits32) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allBits32, allBits32]
  toOrdering (comp m n) === compare m n

prop_mod : Property
prop_mod = property $ do
  [n,d] <- forAll $ np [allBits32, gt0]
  compare (n `mod` d) d === LT

prop_div : Property
prop_div = property $ do
  [n,d] <- forAll $ np [gt0, gt1]
  compare (n `div` d) n === LT

prop_divMod : Property
prop_divMod = property $ do
  [n,d] <- forAll $ np [allBits32, gt0]
  let x = n `div` d
      r = n `mod` d
  n === x * d + r

export
props : Group
props =
  MkGroup "Bits32" $
    [ ("prop_ltMax",  prop_ltMax)
    , ("prop_ltMin",  prop_ltMin)
    , ("prop_comp",   prop_comp)
    , ("prop_mod",    prop_mod)
    , ("prop_div",    prop_div)
    , ("prop_divMod", prop_divMod)
    ] ++ ringProps allBits32
