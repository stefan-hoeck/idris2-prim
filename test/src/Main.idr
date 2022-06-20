module Main

import Char
import Bits8
import Bits16
import Bits32
import Bits64
import Int8
import Int16
import Int32
import Int64
import Int
import Integer
import String
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
  , Int.props
  , Integer.props
  , String.props
  ]
