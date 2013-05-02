{-# LANGUAGE TemplateHaskell #-}

import Test.Framework
import Test.Framework.TH
import Test.Framework.Providers.QuickCheck2

import NanoFeldspar.Core (eval)
import NanoFeldspar.Test



prop_1 a b = eval prog1 a' b == ref a' b
  where
    a' = a `mod` 20
    ref a b = [min (i+3) b | i <- [0..a'-1]]

prop_2 a = eval prog2 a == ref a
  where
    ref a = max (min a a) (min a a)

prop_3 a b = eval prog3 a b' == ref a b'
  where
    b' = a - (b `mod` 20)
    ref a b = sum [l .. u]
      where
        l = min a b
        u = max a b

prop_5 a = eval prog5 a == ref a
  where
    ref a = let (b,c) = (a*2,a*3) in (b-c)*(c-b)

prop_6 = eval prog6 == ref
  where
    ref = as!!1 + sum as + sum as
      where
        as = map (*2) [1..20]

prop_8 a = eval prog8 a == ref a
  where
    ref a = [a .. a+9]



main = $(defaultMainGenerator)

