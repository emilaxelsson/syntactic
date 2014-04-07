{-# LANGUAGE TemplateHaskell #-}

import Test.Tasty
import Test.Tasty.TH
import Test.Tasty.QuickCheck

import NanoFeldspar.Core (eval2)
import NanoFeldspar.Test



prop_scProd a b = eval2 scProd a' b' == ref a' b'
  where
    a' = take 20 a
    b' = take 20 b
    ref a b = sum (zipWith (*) a b)

prop_1 a b = eval2 prog1 a' b == ref a' b
  where
    a' = a `mod` 20
    ref a b = [min (i+3) b | i <- [0..a-1]]

prop_2 a = eval2 prog2 a == ref a
  where
    ref a = max (min a a) (min a a)

prop_3 a b = eval2 prog3 a b' == ref a b'
  where
    b' = a - (b `mod` 20)
    ref a b = sum [l .. u]
      where
        l = min a b
        u = max a b

prop_4 a = eval2 prog4 a' == ref a'
  where
    a' = a `mod` 20
    ref a = [(a+a)*i | i <- [0..a-1]]

prop_5 a = eval2 prog5 a == ref a
  where
    ref a = let (b,c) = (a*2,a*3) in (b-c)*(c-b)

prop_6 = eval2 prog6 == ref
  where
    ref = as!!1 + sum as + sum as
      where
        as = map (*2) [1..20]

prop_8 a = eval2 prog8 a == ref a
  where
    ref a = [a .. a+9]



main = $(defaultMainGenerator)

