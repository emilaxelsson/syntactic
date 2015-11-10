{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module NanoFeldsparTests where



import Control.Monad
import Data.List

import Test.QuickCheck
import Test.Tasty
import Test.Tasty.Golden
import Test.Tasty.QuickCheck

import Data.ByteString.Lazy.UTF8 (fromString)

import Language.Syntactic
import Language.Syntactic.Functional
import qualified NanoFeldspar as Nano



scProd :: [Float] -> [Float] -> Float
scProd as bs = sum $ zipWith (*) as bs

prop_scProd as bs = scProd as bs == Nano.eval Nano.scProd as bs

genMat :: Gen [[Float]]
genMat = sized $ \s -> do
    x <- liftM succ $ choose (0, s `mod` 10)
    y <- liftM succ $ choose (0, s `mod` 10)
    replicateM y $ vector x

forEach = flip map

matMul :: [[Float]] -> [[Float]] -> [[Float]]
matMul a b = forEach a $ \a' ->
               forEach (transpose b) $ \b' ->
                 scProd a' b'

prop_matMul =
    forAll genMat $ \a ->
      forAll genMat $ \b ->
        matMul a b == Nano.eval Nano.matMul a b

mkGold_scProd = writeFile "tests/gold/scProd.txt" $ Nano.showAST Nano.scProd
mkGold_matMul = writeFile "tests/gold/matMul.txt" $ Nano.showAST Nano.matMul

alphaRename :: ASTF Nano.FeldDomain a -> ASTF Nano.FeldDomain a
alphaRename = mapAST rename
  where
    rename :: Nano.FeldDomain a -> Nano.FeldDomain a
    rename s
        | Just (VarT v) <- prj s = inj (VarT (v+1))
        | Just (LamT v) <- prj s = inj (LamT (v+1))
        | otherwise = s

badRename :: ASTF Nano.FeldDomain a -> ASTF Nano.FeldDomain a
badRename = mapAST rename
  where
    rename :: Nano.FeldDomain a -> Nano.FeldDomain a
    rename s
        | Just (VarT v) <- prj s = inj (VarT (v+1))
        | Just (LamT v) <- prj s = inj (LamT (v-1))
        | otherwise = s

prop_alphaEq a = alphaEq a (alphaRename a)

prop_alphaEqBad a = alphaEq a (badRename a)

tests = testGroup "NanoFeldsparTests"
    [ goldenVsString "scProd tree" "tests/gold/scProd.txt" $ return $ fromString $ Nano.showAST Nano.scProd
    , goldenVsString "matMul tree" "tests/gold/matMul.txt" $ return $ fromString $ Nano.showAST Nano.matMul

    , testProperty "scProd eval" prop_scProd
    , testProperty "matMul eval" prop_matMul

    , testProperty "alphaEq scProd"        (prop_alphaEq (desugar Nano.scProd))
    , testProperty "alphaEq matMul"        (prop_alphaEq (desugar Nano.matMul))
    , testProperty "alphaEq scProd matMul" (not (alphaEq (desugar Nano.scProd) (desugar Nano.matMul)))
    , testProperty "alphaEqBad scProd"     (not (prop_alphaEqBad (desugar Nano.scProd)))
    , testProperty "alphaEqBad matMul"     (not (prop_alphaEqBad (desugar Nano.matMul)))
    ]

main = defaultMain tests

