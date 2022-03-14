module Test.Main

import Test.Bits8
import Hedgehog

main : IO ()
main = test
  [ Bits8.props
  ]
