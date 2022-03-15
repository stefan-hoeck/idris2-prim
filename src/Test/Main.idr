module Test.Main

import Test.Char
import Test.Bits8
import Test.Bits16
import Test.Bits32
import Test.Bits64
import Test.Int8
import Test.Int16
import Test.Int32
import Test.Int64
import Test.String
import Hedgehog

main : IO ()
main = test
  [ Char.props
  , Bits8.props
  , Bits16.props
  , Bits32.props
  , Bits64.props
  , Int8.props
  , Int16.props
  , Int32.props
  , Int64.props
  , String.props
  ]
