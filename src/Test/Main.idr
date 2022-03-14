module Test.Main

import Test.Bits8
import Test.Bits16
import Test.Bits32
import Test.Bits64
import Hedgehog

main : IO ()
main = test
  [ Bits8.props
  , Bits16.props
  , Bits32.props
  , Bits64.props
  ]
