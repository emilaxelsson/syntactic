module NanoFeldspar.Test where



import Prelude hiding (length, map, (==), max, min, reverse, sum, unzip, zip, zipWith)

import NanoFeldspar.Core
import NanoFeldspar.Extra
import NanoFeldspar.Vector



--------------------------------------------------------------------------------
-- Basic examples
--------------------------------------------------------------------------------

-- Scalar product
scProd :: Vector (Data Float) -> Vector (Data Float) -> Data Float
scProd a b = sum (zipWith (*) a b)

forEach = flip map

-- Matrix multiplication
matMul :: Matrix Float -> Matrix Float -> Matrix Float
matMul a b = forEach a $ \a' ->
               forEach (transpose b) $ \b' ->
                 scProd a' b'

-- Note that
--
--   * `transpose` is fused with `scProd`
--   * some invariant expressions have been hoisted out of `parallel` and `forLoop` (see the
--     `Let` nodes)
test_matMul = drawAST matMul

-- Parallel array
prog1 :: Data Int -> Data Int -> Data [Int]
prog1 a b = parallel a (\i -> min (i+3) b)

-- Common sub-expressions
prog2 :: Data Int -> Data Int
prog2 a = max (min a a) (min a a)

prog3 :: Data Index -> Data Index -> Data Index
prog3 a b = sum $ reverse (l ... u)
  where
    l = min a b
    u = max a b

-- Invariant code hoisting
prog4 :: Data Int -> Data [Int]
prog4 a = parallel a (\i -> (a+a)*i)

-- Explicit sharing
prog5 :: Data Index -> Data Index
prog5 a = share (a*2,a*3) $ \(b,c) -> (b-c)*(c-b)



--------------------------------------------------------------------------------
-- Common sub-expression elimination and observable sharing
--------------------------------------------------------------------------------

prog6 = index as 1 + sum as + sum as
  where
    as = map (*2) $ force (1...20)

test6_1 = drawAST prog6
  -- Draws a tree with no duplication

test6_2 = drawCSE prog6
  -- Draws a graph with no duplication

test6_3 = drawObs prog6
  -- Draws a graph with some duplication. The 'forLoop' introduced by 'sum' is
  -- not shared, because 'sum as' is repeated twice in source code. But the
  -- 'parallel' introduced by 'force' is shared, because 'force' only appears
  -- once.



--------------------------------------------------------------------------------
-- Optimizations
--------------------------------------------------------------------------------

prog7 :: Data Int -> Data Int
prog7 a = (a==10) ? (max 5 (6+7), max 5 (6+7))

test7 = drawSimp prog7
  -- Reduced to the literal 13

prog8 a = c ? (parallel 10 (+a), parallel 10 (+a))
  where
    c = (a*a*a*a) == 23

test8 = drawSimp prog8
  -- The condition gets pruned away

