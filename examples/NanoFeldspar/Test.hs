module NanoFeldspar.Test where



import Prelude hiding (length, map, (==), max, min, reverse, sum, unzip, zip, zipWith)

import NanoFeldspar.Core
import NanoFeldspar.Extra
import NanoFeldspar.Vector



--------------------------------------------------------------------------------
-- Basic operations
--------------------------------------------------------------------------------

-- Parallel arrays
prog1 :: Data Int -> Data Int -> Data [Int]
prog1 a b = parallel a (\i -> min (i+3) b)

-- Evaluation
test1_1 = eval prog1 10 20

-- Print the expression
test1_2 = printExpr prog1

-- Render the syntax tree
test1_3 = drawAST prog1

-- Common sub-expressions
prog2 :: Data Int -> Data Int
prog2 a = max (min a a) (min a a)

-- Basic vector operations
prog3 :: Data Index -> Data Index -> Data Index
prog3 a b = sum $ reverse (l ... u)
  where
    l = min a b
    u = max a b

-- Explicit sharing
prog4 :: Data Index -> Data Index
prog4 a = share (a*2,a*3) $ \(b,c) -> (b-c)*(c-b)



--------------------------------------------------------------------------------
-- Common sub-expression elimination and observable sharing
--------------------------------------------------------------------------------

prog5 = index as 1 + sum as + sum as
  where
    as = map (*2) $ force (1...20)

test5_1 = drawAST prog5
  -- Draws a tree with no duplication

test5_2 = drawCSE prog5
  -- Draws a graph with no duplication

test5_3 = drawObs prog5
  -- Draws a graph with some duplication. The 'forLoop' introduced by 'sum' is
  -- not shared, because 'sum as' is repeated twice in source code. But the
  -- 'parallel' introduced by 'force' is shared, because 'force' only appears
  -- once.



--------------------------------------------------------------------------------
-- Optimizations
--------------------------------------------------------------------------------

prog6 :: Data Int -> Data Int
prog6 a = (a==10) ? (max 5 (6+7), max 5 (6+7))

test6 = drawPart prog6
  -- Reduced to the literal 13

prog7 a = c ? (parallel 10 (+a), parallel 10 (+a))
  where
    c = (a*a*a*a) == 23

test7 = drawPart prog7
  -- The condition gets pruned away

