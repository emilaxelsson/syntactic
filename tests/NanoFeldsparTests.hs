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
import Language.Syntactic.Functional.Sharing
import qualified NanoFeldspar as Nano



-- | Evaluate after code motion. Used to test that 'codeMotion' doesn't change
-- semantics.
evalCM :: (Syntactic a, Domain a ~ Nano.FeldDomain) => a -> Internal a
evalCM = evalClosed . codeMotion Nano.cmInterface . desugar

fib :: Int -> Int
fib n = fibs !! n
  where
    fibs = 0 : 1 : zipWith (+) fibs (tail fibs)

prop_fib (NonNegative (Small n))   = fib n == Nano.eval Nano.fib n
prop_fibCM (NonNegative (Small n)) = fib n == evalCM Nano.fib n

spanVec :: [Int] -> Int
spanVec as = maximum as - minimum as

prop_spanVec (NonEmpty as)   = spanVec as == Nano.eval Nano.spanVec as
prop_spanVecCM (NonEmpty as) = spanVec as == evalCM Nano.spanVec as

scProd :: [Float] -> [Float] -> Float
scProd as bs = sum $ zipWith (*) as bs

prop_scProd as bs   = scProd as bs == Nano.eval Nano.scProd as bs
prop_scProdCM as bs = scProd as bs == evalCM Nano.scProd as bs

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

prop_matMulCM =
    forAll genMat $ \a ->
      forAll genMat $ \b ->
        matMul a b == evalCM Nano.matMul a b

alphaRename :: ASTF Nano.FeldDomain a -> ASTF Nano.FeldDomain a
alphaRename = mapAST rename
  where
    rename :: Nano.FeldDomain a -> Nano.FeldDomain a
    rename (Typed s)
        | Just (VarT v) <- prj s = Typed $ inj (VarT (v+1))
        | Just (LamT v) <- prj s = Typed $ inj (LamT (v+1))
        | otherwise = Typed s

badRename :: ASTF Nano.FeldDomain a -> ASTF Nano.FeldDomain a
badRename = mapAST rename
  where
    rename :: Nano.FeldDomain a -> Nano.FeldDomain a
    rename (Typed s)
        | Just (VarT v) <- prj s = Typed $ inj (VarT (v+1))
        | Just (LamT v) <- prj s = Typed $ inj (LamT (v-1))
        | otherwise = Typed s

prop_alphaEq a = alphaEq a (alphaRename a)

prop_alphaEqBad a = alphaEq a (badRename a)

tests = testGroup "NanoFeldsparTests"
    [ goldenVsString "fib tree"     "tests/gold/fib.txt"     $ return $ fromString $ Nano.showAST Nano.fib
    , goldenVsString "spanVec tree" "tests/gold/spanVec.txt" $ return $ fromString $ Nano.showAST Nano.spanVec
    , goldenVsString "scProd tree"  "tests/gold/scProd.txt"  $ return $ fromString $ Nano.showAST Nano.scProd
    , goldenVsString "matMul tree"  "tests/gold/matMul.txt"  $ return $ fromString $ Nano.showAST Nano.matMul

    , testProperty "fib eval"     prop_fib
    , testProperty "spanVec eval" prop_spanVec
    , testProperty "scProd eval"  prop_scProd
    , testProperty "matMul eval"  prop_matMul

    , testProperty "fib evalCM"    prop_fibCM
    , testProperty "scProd evalCM" prop_scProdCM
    , testProperty "matMul evalCM" prop_matMulCM

    , testProperty "alphaEq scProd"        (prop_alphaEq (desugar Nano.scProd))
    , testProperty "alphaEq matMul"        (prop_alphaEq (desugar Nano.matMul))
    , testProperty "alphaEq scProd matMul" (not (alphaEq (desugar Nano.scProd) (desugar Nano.matMul)))
    , testProperty "alphaEqBad scProd"     (not (prop_alphaEqBad (desugar Nano.scProd)))
    , testProperty "alphaEqBad matMul"     (not (prop_alphaEqBad (desugar Nano.matMul)))
    ]

main = defaultMain tests

