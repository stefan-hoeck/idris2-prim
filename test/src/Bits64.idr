module Bits64

import Data.Prim.Bits64
import Data.SOP
import Hedgehog
import RingLaws

allBits64 : Gen Bits64
allBits64 = bits64 (linear 0 0xffffffffffffffff)

gt0 : Gen Bits64
gt0 = bits64 (linear 1 MaxBits64)

gt1 : Gen Bits64
gt1 = bits64 (linear 2 MaxBits64)

prop_ltMax : Property
prop_ltMax = property $ do
  b8 <- forAll allBits64
  (b8 <= MaxBits64) === True

prop_ltMin : Property
prop_ltMin = property $ do
  b8 <- forAll allBits64
  (b8 >= MinBits64) === True

prop_comp : Property
prop_comp = property $ do
  [m,n] <- forAll $ np [allBits64, allBits64]
  toOrdering (comp m n) === compare m n

prop_mod : Property
prop_mod = property $ do
  [n,d] <- forAll $ np [allBits64, gt0]
  compare (n `mod` d) d === LT

prop_div : Property
prop_div = property $ do
  [n,d] <- forAll $ np [gt0, gt1]
  compare (n `div` d) n === LT

prop_divMod : Property
prop_divMod = property $ do
  [n,d] <- forAll $ np [allBits64, gt0]
  let x = n `div` d
      r = n `mod` d
  n === x * d + r

export
props : Group
props =
  MkGroup "Bits64" $
    [ ("prop_ltMax",  prop_ltMax)
    , ("prop_ltMin",  prop_ltMin)
    , ("prop_comp",   prop_comp)
    , ("prop_mod",    prop_mod)
    , ("prop_div",    prop_div)
    , ("prop_divMod", prop_divMod)
    ] ++ ringProps allBits64
