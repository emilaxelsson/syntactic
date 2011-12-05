module Main where

import qualified Prelude
import MuFeldspar.Prelude

import MuFeldspar.Core
import MuFeldspar.Frontend
import MuFeldspar.Vector

import Imperative.Imperative
import Imperative.Compiler

import Data.Word
import Data.Bits (Bits)


type VecBool = Vector (Data Bool)

type VecInt = Vector (Data Int)

-- Primitive Functions (and tuples)

prog0 :: Data Int -> Data Int
prog0 = (*2)

prog1 :: (Data Int, Data Int) -> (Data Int, Data Int, Data Int)
prog1 (a,b) = (min a b, a + b, a ^ b)

prog2 :: Data Int -> Data Int -> (Data Int, Data Int, Data Int)
prog2 a b = (min a b, a + b, a ^ b)

isEven :: (Type a, Integral a) => Data a -> Data Bool
isEven i = i `mod` 2 == 0

swap (a,b) = (b,a)


-- Conditional

f :: Data Int -> Data Int
f i = (isEven i) ? (2*i, i)

t1 = eval (f 3)

t2 = eval (f 4)


-- Arrays

prog3 :: Data [Int]
prog3 = parallel 10 (*2)

tst1 = eval prog3

tst1a = drawFeld prog3

tst1b = printFeld prog3

tst1c = compile prog3

prog4 :: Data [Int]
prog4 = parallel 10 (`mod` 5)

prog5 :: Data [Int]
prog5 = parallel 10 f

prog6 :: Data [Int]
prog6 = parallel 10 (<< 3)

prog7 :: Data [Int]
prog7 = parallel 10 (>> 1)

prog8 :: Data [Int]
prog8 = parallel 12 (`xor` 3)




perm f arr = parallel (getLength arr) (\i -> getIx arr (f i))

rot arr = perm f arr
  where
    f i = (i+1) `mod` (getLength arr)

prog9 :: Data [[Int]]
prog9 = parallel 8 (\i -> parallel i id)

-- Sequential Arrays

prog10 :: Data [Int]
prog10 = sequential 10 1 g
  where
    g ix st = (j,j) 
      where j = (ix + 1)  * st

-- for Loop

prog11 :: Data Int -> Data Int
prog11 k  = forLoop k 1 g
  where
    g ix st = (ix + 1) * st

composeN :: (Syntax st) => (st -> st) -> Data Length -> st -> st
composeN f l i0 = forLoop l i0 g
  where
    g _ i = f i

ccn = compile (composeN ((*2) :: Data Int -> Data Int))





-- Vectors

prog12 :: Vector (Data Int)
prog12 = Indexed 10 (*2)

tst2 = eval prog11

prog13 :: Data Int
prog13 = sum $ Indexed 10 (*2)


prog14 :: Vector (Data Int)
prog14 = map (*5) $ Indexed 10 (*2)

prog15 :: Vector (Data Int)
prog15 = map (*5) . map (+1) $ Indexed 10 (*2)

scalarProduct :: (Type a, Num a) => Vector (Data a) -> Vector (Data a) -> Data a
scalarProduct as bs = sum $ zipWith (*) as bs


forceEx as bs = (sum . force) $ zipWith (*) as bs

prog16 :: Data Int -> Data Int
prog16 a = sum $ (isEven a) ? (prog14, prog15)





sumEven :: VecInt -> Data Int
sumEven = sum . map zeroOutOdd
  where
    zeroOutOdd x = (testBit x 0) ? (0,x)

{--
*Main> eval $ sumEven (value [1..10])
30
--}





testBit :: (Type a, Bits a) => Data a -> Data Index -> Data Bool
testBit l i = not ((l .&. (1<<i)) == 0)

int2BLN :: Data Length -> Data Int -> VecBool
int2BLN n v = reverse $ indexed n (testBit v)

int2BL :: (Type a, Bits a)  =>  Data a -> VecBool
int2BL l = reverse $ indexed (bitSize l) (testBit l)



dft :: Vector (Data Complex) -> Vector (Data Complex)
dft v = Indexed l ixf
  where
    l = length v
    ixf i = scalarProduct v (ts i)
    ts k = indexed l f
      where f i = cis $ (-2 * (value pi) * (i2n i) * (i2n k)) / (i2n l)