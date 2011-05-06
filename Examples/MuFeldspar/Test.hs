import Prelude hiding (length, map, max, min, reverse, sum, unzip, zip)

import Language.Syntactic.Features.Binding.HigherOrder

import MuFeldspar.Core
import MuFeldspar.Vector



prog1 :: Data Int -> Data Int -> Data Int
prog1 a b = min (max a (getIx (parallel b (\i -> min i b)) 3)) 2

test1_1 = drawAST $ reify $ lambdaN prog1
test1_2 = printExpr $ reify $ lambdaN prog1
test1_3 = eval $ prog1 0 10

prog2 :: Data Int -> Data Int
prog2 a = let_ (min a a) $ \b -> max b b

test2_1 = drawAST $ reify $ lambdaN prog2
test2_2 = printExpr $ reify $ lambdaN prog2
test2_3 = eval $ prog2 34

prog3 :: Data Index
prog3 = sum $ reverse (10...45)

test3_1 = drawAST $ reify prog3
test3_2 = printExpr $ reify prog3
test3_3 = eval prog3
test3_4 = eval (forLoop ((45 - 10) + 1) 0 (\var0 -> (\var1 -> ((((((45 - 10) + 1) - var0) - 1) + 10) + var1))))
  -- Pasted in the result of 'test3_2'

prog4 :: Vector (Data Index)
prog4 = map (uncurry (*)) $ zip (1...1000) (vector [34,43,52,61])

test4_1 = drawAST $ reify $ desugar prog4
test4_2 = printExpr $ reify $ desugar prog4
test4_3 = eval $ desugar prog4

