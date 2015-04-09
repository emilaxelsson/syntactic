{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module MonadTests where



import Test.Tasty
import Test.Tasty.Golden

import Data.ByteString.Lazy.UTF8 (fromString)

import Data.Syntactic
import qualified Monad



mkGold_ex1 = writeFile "tests/gold/ex1_Monad.txt" $ showAST $ desugar Monad.ex1

tests = testGroup "MonadTests"
    [ goldenVsString "ex1 tree" "tests/gold/ex1_Monad.txt" $ return $ fromString $ showAST $ desugar Monad.ex1
    ]

main = defaultMain tests

