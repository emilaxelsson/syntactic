{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module WellScopedTests where



import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.QuickCheck

import Data.ByteString.Lazy.UTF8 (fromString)

import Language.Syntactic
import Language.Syntactic.Functional
import qualified WellScoped as WS



ex1 a = let b = a+4 in let c = a+b in a+b+c

prop_ex1 a = ex1 a == evalClosedWS WS.ex1 a

mkGold_ex1 = writeFile "tests/gold/ex1_WS.txt" $ showAST $ fromWS WS.ex1

tests = testGroup "WellScopedTests"
    [ goldenVsString "ex1 tree" "tests/gold/ex1_WS.txt" $ return $ fromString $ showAST $ fromWS WS.ex1
    , testProperty   "ex1" prop_ex1
    ]

main = defaultMain tests

