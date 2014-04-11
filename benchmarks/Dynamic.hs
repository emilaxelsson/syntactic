{-# OPTIONS_GHC -fcontext-stack=100 #-}

module Dynamic where

import Criterion.Main
import Criterion.Config
import Data.Monoid
import Data.Syntactic
import Data.Syntactic.TypeUniverse

import qualified Data.Dynamic as Base  -- For comparison



type Types  = BoolType :+: IntType :+: ListType

type Types2 = CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: CharType :+: BoolType :+: IntType
  -- 30 terms

dynList :: Int -> [Dynamic Types]
dynList n = concat [[toDyn i, toDyn (even i)] | i <- [0..n]]

dynList2 :: Int -> [Dynamic Types2]
dynList2 n = concat [[toDyn i, toDyn (even i)] | i <- [0..n]]

dynListBase :: Int -> [Base.Dynamic]
dynListBase n = concat [[Base.toDyn i, Base.toDyn (even i)] | i <- [0..n]]

dynSum :: [Dynamic Types] -> Int
dynSum ds = sum [i | d <- ds, Just i <- [fromDyn d]]

dynSum2 :: [Dynamic Types2] -> Int
dynSum2 ds = sum [i | d <- ds, Just i <- [fromDyn d]]

dynSumBase :: [Base.Dynamic] -> Int
dynSumBase ds = sum [i | d <- ds, Just i <- [Base.fromDynamic d]]

testDyn :: Int -> Int
testDyn = dynSum . dynList

testDyn2 :: Int -> Int
testDyn2 = dynSum2 . dynList2

testDynBase :: Int -> Int
testDynBase = dynSumBase . dynListBase

main :: IO ()
main = defaultMainWith (defaultConfig {cfgSummaryFile = Last $ Just "bench-results/dynamic.csv"}) (return ())
    [ bgroup "size=1000"
       [ bench "testDyn"     $ nf testDyn     1000
       , bench "testDyn2"    $ nf testDyn2    1000
       , bench "testDynBase" $ nf testDynBase 1000
       ]
    , bgroup "size=2000"
       [ bench "testDyn"     $ nf testDyn     2000
       , bench "testDyn2"    $ nf testDyn2    2000
       , bench "testDynBase" $ nf testDynBase 2000
       ]
    ]
