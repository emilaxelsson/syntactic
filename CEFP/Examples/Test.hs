import qualified Prelude

import MuFeldspar.Prelude
import MuFeldspar.Core
import MuFeldspar.Frontend
import MuFeldspar.Vector

import Imperative.Imperative
import Imperative.Compiler



prog1 :: Data Int
prog1 = 23 + min 45 2

test1_1 = eval prog1
test1_2 = printMain $ compile prog1

prog2 = (prog1==3) ? (prog1*3, prog1*4)

test2_1 = eval prog2
test2_2 = printMain $ compile prog2
  -- Note how prog1 is only computed once

prog3 :: Vector (Vector (Data Int)) -> Vector (Vector (Data Int))
prog3 = map reverse . map reverse

test3_1 = eval prog3 [[1,2,3],[4,5],[6]]
test3_2 = printMain $ compile prog3

prog4 :: Vector (Vector (Data Int)) -> Data Int
prog4 = sum . map sum . map reverse . map reverse

test4_1 = eval prog4 [[1,2,3],[4,5],[6]]
test4_2 = printMain $ compile prog4

prog5 = sequential 10 1 $ \i st -> (i+st, (i+1)*st)

test5_1 = eval prog5
test5_2 = printMain $ compile prog5

prog6 as bs = sum (zipWith (*) as bs) :: Data Index

test6_1 = eval prog6 [10..19] [20..29]
test6_2 = printMain $ compile prog6

