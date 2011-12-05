module Main where

import qualified Prelude

import MuFeldspar.Prelude


import MuFeldspar.Core
--import MuFeldspar.Tuple
import MuFeldspar.Frontend
import MuFeldspar.Vector


import Imperative.Imperative
import Imperative.Compiler

import Data.Word
import Data.Bits (Bits)

type VecBool = Vector (Data Bool)

type VecInt = Vector (Data Int)



-- Exercise 1

composeN :: (Syntax st) => (st -> st) -> Data Length -> st -> st
composeN f l i0 = forLoop l i0 g
  where
    g _ st = f st

tri :: (Syntax a) => (a -> a)  -> Vector a -> Vector a
tri f (Indexed len ixf) = indexed len ixf'
  where
    ixf' i = composeN f i (ixf i)


tri1 :: (Syntax a) => (a -> a)  -> Vector a -> Vector a
tri1 f (Indexed len ixf) = indexed len ixf'
  where
    ixf' i = forLoop i (ixf i) (\_ -> f)


{--
*Main> eval $ tri (*2) (1...6)
[1,4,12,32,80,192]
*Main> eval $ tri1 (*2) (1...6)
[1,4,12,32,80,192]
--}


-- Exercise 2

swapOE1 :: (Syntax a) => Vector a -> Vector a
swapOE1 v = Indexed (length v) ixf
  where
    ixf i = (i `mod` 2 == 0) ? (index v (i+1), index v (i-1))

-- same as above
swapOE2 :: Vector a -> Vector a
swapOE2 = premap (\i -> (i `mod` 2 == 0) ?  (i+1,i-1))

swapOE3 :: Vector a -> Vector a
swapOE3 = premap (`xor` 1)

premap :: (Data Index -> Data Index) -> Vector a -> Vector a
premap f (Indexed l ixf) = Indexed l (ixf . f)



-- Exercise 3

pows2 :: Data Int -> Vector (Data Int)
pows2 k = Indexed k (2^)    



pow2 :: Data Index -> Data Index
pow2 k = 1 << k                   -- or  2^k    

pows21 :: Data Length -> Vector (Data Index)
pows21 k = Indexed k pow2   





-- Exercise 4

pad :: Data Length -> VecBool -> VecBool
pad l v = (replicate (l - length v) false) ++ v

xorBool :: Data Bool -> Data Bool -> Data Bool
xorBool a b = not (a == b)

crcAdd :: VecBool -> VecBool -> VecBool
crcAdd as bs = zipWith xorBool (pad m as) (pad m bs)
  where
    m = max (length as) (length bs)






-- Exercise 5

-- direct implementation using reverseBits
bitr :: Data Index -> Data Index -> Data Index
bitr n a =
    share (oneBitsN n) $ \mask -> (complement mask .&. a) .|. rev mask
  where
    rev mask = rotateL (reverseBits (mask .&. a)) n

bitRev :: Data Index -> Vector a -> Vector a
bitRev n = premap (bitr n)

oneBitsN :: Data Index -> Data Index
oneBitsN  = complement . zeroBitsN

zeroBitsN :: Data Index -> Data Index
zeroBitsN = shiftL allOnes

allOnes :: Data Index
allOnes = complement 0



bitrH :: Index -> Data Index -> Data Index
bitrH n  a =
    share (oneBitsN vn) $ \mask -> (complement mask .&. a) .|. rev mask
  where
    rev mask = rotateL (reverseBits (mask .&. a)) vn
    vn = value n





-- transliteration of solution from bithacks
bitr1 :: Data Index -> Data Index -> Data Index
bitr1 n i = snd (pipe stage (countUp n) (i, i >> n))
  where
    stage _ (i,r) = (i>>1, (i .&. 1) .|. (r<<1))

bitRev1 :: Data Index -> Vector a -> Vector a
bitRev1 n = premap (bitr1 n)

countUp :: Data Length -> Vector (Data Index)
countUp n = Indexed n id

pipe :: Syntax a => (Data Index -> a -> a) -> Vector (Data Index) -> a -> a
pipe = flip . fold . flip 



-- A version of composeN that depends on a *Haskell* value

composeNH :: Index -> (a -> a) -> a -> a
composeNH 0 f = id
composeNH n f = (composeNH (n-1) f) . f


-- Now use this to make bitr. Note the type.

bitr1H :: Index -> Data Index -> Data Index
bitr1H n i = snd (composeNH n stage (i, i >> vn))
  where
    stage (i,r) = (i>>1, (i .&. 1) .|. (r<<1))
    vn = value n


-- Now we must provide the n parameter at compile time
-- and the recursion gets unwound

{--

main (v0)
  x3 := v0
  x4 := 1 :: Int
  x2 := (shiftR x3 x4)
  x5 := 1 :: Int
  x1 := (shiftR x2 x5)
  x6 := 1 :: Int
  x0 := (x1 .&. x6)
  x11 := v0
  x12 := 1 :: Int
  x10 := (shiftR x11 x12)
  x13 := 1 :: Int
  x9 := (x10 .&. x13)
  x17 := v0
  x18 := 1 :: Int
  x16 := (x17 .&. x18)
  x21 := v0
  x22 := 3 :: Int
  x20 := (shiftR x21 x22)
  x23 := 1 :: Int
  x19 := (shiftL x20 x23)
  x15 := (x16 .|. x19)
  x24 := 1 :: Int
  x14 := (shiftL x15 x24)
  x8 := (x9 .|. x14)
  x25 := 1 :: Int
  x7 := (shiftL x8 x25)
  out := (x0 .|. x7)


Compare with  printMain $ bitr1
which gives the expected for loop

main (v0,v1)
  x1 := v0
  x2 := v1
  x4 := v1
  x5 := v0
  x3 := (shiftR x4 x5)
  v3 := (tup2 x2 x3)

  for v2 in 0 .. (x1-1) do
    x8 := v3
    x7 := (sel1 x8)
    x9 := 1 :: Int
    x6 := (shiftR x7 x9)
    x13 := v3
    x12 := (sel1 x13)
    x14 := 1 :: Int
    x11 := (x12 .&. x14)
    x17 := v3
    x16 := (sel2 x17)
    x18 := 1 :: Int
    x15 := (shiftL x16 x18)
    x10 := (x11 .|. x15)
    v3 := (tup2 x6 x10)
  x0 := v3
  out := (sel2 x0)

--}






specbr m n v = bL2Int (l ++ r')
  where
    iv = int2BLN m v
    (l,r) = splitAt (m-n) iv
    r' = reverse r

testBit :: (Type a, Bits a) => Data a -> Data Index -> Data Bool
testBit l i = not ((l .&. (1<<i)) == 0)


int2BL :: (Type a, Bits a)  =>  Data a -> VecBool
int2BL l = reverse $ indexed (bitSize l) (testBit l)


int2BLN :: Data Length -> Data Int -> VecBool
int2BLN n v = reverse $ indexed n (testBit v)


bL2Int :: VecBool -> Data Int
bL2Int bs = scalarProduct (reverse (map b2i bs)) (pows2 (length bs))

bL2Int' :: VecBool -> Data Int
bL2Int' = sum . tri (*2) . map b2i

scalarProduct :: (Type a, Num a) => Vector (Data a) -> Vector (Data a) -> Data a
scalarProduct as bs = sum (zipWith (*) as bs)





-- Exercise 6   (See slides)

-- 2^n input FFT. Applies to sub-parts of input vector
-- of length 2^(n+i). 
-- There is currently no check that the input vector is at least of length 2^n


countDown n = reverse (indexed n id)

fft :: Data Index ->  Vector (Data Complex) -> Vector (Data Complex)
fft n = bitRev n . lin stage (countDown n)
  where
    stage k = combx f g (bitZero k) (flipBit k) twid 
      where
        f a b _ = a + b
        g a b t = t * (a-b)
        twid i  = cis ((-(value pi)*(i2n (lsbsN k i)))/  i2n (pow2 k))



combx f g c p x (Indexed l ixf) =  Indexed l ixf'
      where
        ixf' i = (c i) ? (f ai pi xi, g pi ai xi)
          where
            ai = ixf i
            pi = ixf (p i)
            xi = x i




lin :: Syntax a => (b -> a -> a) -> Vector b -> a -> a
lin f (Indexed len ixf) a = forLoop len a (\i st -> f (ixf i) st)

lsbsN :: Data Index -> Data Index -> Data Index
lsbsN k i = i .&. oneBitsN k

bitZero :: Data Index -> Data Index -> Data Bool
bitZero k i = (i .&. (1<<k)) == 0

flipBit ::  Data Index -> Data Index -> Data Index
flipBit k = (`xor` (1<<k))




-- Exercise 7 bitonic sort

-- bitonic merge (see slides)

comb :: (Syntax a) =>
        (t -> t -> a) -> (t -> t -> a)
         -> (Data Index -> Data Bool) -> (Data Index -> Data Index)
         -> Vector t 
         -> Vector a
comb f g c p (Indexed l ixf) = Indexed l ixf'
  where
    ixf' i = (c i) ? (f a b, g a b)
      where
        a = ixf i
        b = ixf (p i)

apart :: (Syntax a) =>
         (t -> t -> a) -> (t -> t -> a)
         -> Data Index
         -> Vector t
         -> Vector a
apart f g k = comb f g (bitZero k) (flipBit k)






bMerge :: Data Index -> Vector (Data Int) -> Vector (Data Int)
bMerge n = lin (apart min max) (countDown n)
  

-- now we'd like to be able to reverse half of each 2^n length sub-vector

halfRev :: Data Index -> Vector (Data a) -> Vector (Data a)
halfRev n = premap (\i -> (bitZero n' i) ? (i ,i `xor` oneBitsN n'))
  where
    n' = n-1


merge :: Data Index -> Vector (Data Int) -> Vector (Data Int)
merge n = bMerge n . halfRev n 

bsort :: Data Index -> Vector (Data Int) -> Vector (Data Int)
bsort n = lin merge (1...n)




