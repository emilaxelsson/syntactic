{-# LANGUAGE GADTs, TypeOperators, TemplateHaskell #-}
module WithArity (main) where

import Criterion.Main
import Criterion.Config
import Data.Monoid
import Data.Syntactic hiding (E)

main :: IO ()
main = defaultMainWith (defaultConfig {cfgSummaryFile = Last $ Just "bench-results/withArity.csv"}) (return ())
         [ bgroup "eval 5"  [ bench "gadt"      $ nf evl (gExpr 5)
                            , bench "Syntactic" $ nf evaluate (sExpr 5) ]
         , bgroup "eval 6"  [ bench "gadt"      $ nf evl (gExpr 6)
                            , bench "Syntactic" $ nf evaluate (sExpr 6) ]
         , bgroup "eval 7"  [ bench "gadt"      $ nf evl (gExpr 7)
                            , bench "Syntactic" $ nf evaluate (sExpr 7) ]
         , bgroup "size 5"  [ bench "gadt"      $ nf gSize (gExpr 5)
                            , bench "Syntactic" $ nf size (sExpr 5) ]
         , bgroup "size 6"  [ bench "gadt"      $ nf gSize (gExpr 6)
                            , bench "Syntactic" $ nf size (sExpr 6) ]
         , bgroup "size 7"  [ bench "gadt"      $ nf gSize (gExpr 7)
                            , bench "Syntactic" $ nf size (sExpr 7) ]]


-- Expressions
gExpr :: Int -> E Int
gExpr 0  = E0 1
gExpr 1  = E2 (E2 (E0 1) (E0 1)) (E1 (E0 1))
gExpr n  = E10 (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1))
           (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1)) (gExpr (n-1))

sExpr :: Int -> T' Int
sExpr 0  = t0 1
sExpr 1  = t2 (t2 (t0 1) (t0 1)) (t1 (t0 1))
sExpr n  = t10 (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1))
           (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1)) (sExpr (n-1))

gSize :: E a -> Int
gSize (E0 _) = 1
gSize (E1 a)   = gSize a
gSize (E2 a b) = gSize a + gSize b
gSize (E3 a b c) = gSize a + gSize b + gSize c
gSize (E5 a b c d e) = gSize a + gSize b + gSize c + gSize d + gSize e
gSize (E10 a b c d e f g h i j) = gSize a + gSize b + gSize c + gSize d + gSize e +
                                  gSize f + gSize g + gSize h + gSize i + gSize j


-- Comparing Syntactic with GADTs
-- GADTs
data E a where
  E0    :: a  -> E a
  E1    :: E a -> E a
  E2    :: E a -> E a -> E a
  E3    :: E a -> E a -> E a -> E a
  E5    :: E a -> E a -> E a -> E a -> E a -> E a
  E10   :: E a -> E a -> E a -> E a -> E a -> E a -> E a -> E a -> E a -> E a -> E a


evl :: E Int -> Int
evl (E0 n)         =  n
evl (E1 a)         =  evl a
evl (E2 a b)       =  evl a + evl b
evl (E3 a b c)     =  evl a + evl b + evl c
evl (E5 a b c d e) =  evl a + evl b + evl c + evl d + evl e
evl (E10 a b c d e f g h i j) =
    evl a + evl b + evl c + evl d + evl e + evl f + evl g + evl h + evl i + evl j

-- Syntactic

data T a where
  T0    :: Num a =>  a  -> T (Full a)
  T1    :: Num a =>  T (a :-> Full a)
  T2    :: Num a =>  T (a :-> a :-> Full a)
  T3    :: Num a =>  T (a :-> a :-> a :-> Full a)
  T5    :: Num a =>  T (a :-> a :-> a :-> a :-> a :-> Full a)
  T10   :: Num a =>  T (a :-> a :-> a :-> a :-> a :-> a :-> a :-> a :-> a :-> a :-> Full a)

type T' a = AST T (Full a)

t0  :: Num a =>  a -> T' a
t0 = Sym . T0

t1 :: Num a =>  T' a -> T' a
t1 a = Sym T1 :$ a

t2    :: Num a =>  T' a -> T' a -> T' a
t2 a b = Sym T2 :$ a :$ b

t3    :: Num a =>  T' a -> T' a -> T' a -> T' a
t3 a b c = Sym T3 :$ a :$ b :$ c

t5    :: Num a =>  T' a -> T' a -> T' a -> T' a -> T' a -> T' a
t5 a b c d e = Sym T5 :$ a :$ b :$ c :$ d :$ e

t10   :: Num a => T' a -> T' a -> T' a -> T' a -> T' a -> T' a -> T' a -> T' a -> T' a -> T' a -> T' a
t10 a b c d e f g h i j = Sym T10 :$ a :$ b :$ c :$ d :$ e :$ f :$ g :$ h :$ i:$ j

instance Default T
    where
      defaultSym (T0 a) = Def "T0"  a
      defaultSym T1     = Def "T1"  id
      defaultSym T2     = Def "T2"  (+)
      defaultSym T3     = Def "T3"  (\a b c -> a + b + c)
      defaultSym T5     = Def "T5"  (\a b c d e -> a + b + c + d + e)
      defaultSym T10    = Def "T10" (\a b c d e f g h i j ->
                                        a + b + c + d + e + f + g + h + i + j)

interpretationInstances ''T

