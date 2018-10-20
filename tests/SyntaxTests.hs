{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module SyntaxTests where

import Data.Maybe
import Language.Syntactic
import Language.Syntactic.TH
import Test.Tasty
import Test.Tasty.HUnit

data A sig
  where
    A1 :: Int -> A (Full Int)
    A2 :: A (Int :-> Full Int)

deriving instance Eq (A sig)
deriving instance Show (A sig)

data B sig
  where
    B1 :: Char -> B (Full Char)

deriving instance Eq (B sig)
deriving instance Show (B sig)

data C sig
  where
    C1 :: C (Full ())
    C2 :: C (Int :-> Int :-> Full Int)

deriving instance Eq (C sig)
deriving instance Show (C sig)

type Dom = A :+: B :+: C

type Exp a = ASTF Dom a

a1 :: Int -> Exp Int
a1 = inj . A1

a2 :: Exp Int -> Exp Int
a2 a = inj A2 :$ a

b1 :: Char -> Exp Char
b1 = inj . B1

c1 :: Exp ()
c1 = inj $ C1

c2 :: Exp Int -> Exp Int -> Exp Int
c2 a b = inj C2 :$ a :$ b

tests = testGroup "SyntaxTests"
  [
    testCase "project first domain entry 1" $ prj (a1 5)      @?= Just (A1 5)
  , testCase "project first domain entry 2" $ prj (a2 (a1 1)) @?= (Nothing :: Maybe (A (Full Int)))
  , testCase "project second domain entry"  $ prj (b1 'b')    @?= Just (B1 'b')
  , testCase "project third domain entry 1" $ prj (c1)        @?= Just C1
  , testCase "project third domain entry 2" $ prj (c2 (a1 3) (a2 (a1 9))) @?= (Nothing :: Maybe (C (Full Int)))
  ]
