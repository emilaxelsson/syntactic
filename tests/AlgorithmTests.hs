{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module AlgorithmTests where



import Data.List
import qualified Data.Set as Set
import Data.Dynamic

import Language.Syntactic
import Language.Syntactic.TH
import Language.Syntactic.Functional
import Language.Syntactic.Functional.Sharing

import Test.QuickCheck

import Test.Tasty.QuickCheck
import Test.Tasty.TH



data Sym sig
  where
    Int   :: Int -> Sym (Full Int)
    Neg   :: Sym (Full (Int -> Int))
    Add   :: Sym (Full (Int -> Int -> Int))
    App1  :: Sym ((Int -> Int) :-> Int :-> Full Int)
    App2  :: Sym ((Int -> Int -> Int) :-> Int :-> Int :-> Full Int)
    App3  :: Sym ((Int -> Int -> Int -> Int) :-> Int :-> Int :-> Int :-> Full Int)

deriveSymbol    ''Sym
deriveRender id ''Sym
deriveEquality  ''Sym

instance StringTree Sym
instance EvalEnv Sym env

instance Eval Sym
  where
    evalSym (Int i) = i
    evalSym Neg     = negate
    evalSym Add     = (+)
    evalSym App1    = ($)
    evalSym App2    = \f a b -> f a b
    evalSym App3    = \f a b c -> f a b c

type Dom = Typed (BindingT :+: Let :+: Sym)

type Exp a = ASTF Dom a

int :: Int -> Exp Int
int = sugarSymTyped . Int

neg :: Exp Int -> Exp Int
neg = app1 (sugarSymTyped Neg)

add :: Exp Int -> Exp Int -> Exp Int
add = app2 (sugarSymTyped Add)

app1 :: Exp (Int -> Int) -> Exp Int -> Exp Int
app1 = sugarSymTyped App1

app2 :: Exp (Int -> Int -> Int) -> Exp Int -> Exp Int -> Exp Int
app2 = sugarSymTyped App2

app3 :: Exp (Int -> Int -> Int -> Int) -> Exp Int -> Exp Int -> Exp Int -> Exp Int
app3 = sugarSymTyped App3

varr :: Name -> Exp Int
varr = sugarSymTyped . VarT

lamm :: Typeable a => Name -> Exp a -> Exp (Int -> a)
lamm v = sugarSymTyped (LamT v)



-- | Return a 'Name' not in the given list
notIn :: [Name] -> Name
notIn = go 0 . sort
  where
    go prev [] = prev+1
    go prev (n:ns)
        | n > prev+1 = prev+1
        | otherwise  = go n ns

-- | Generate a variable name
genVar
    :: Int     -- ^ Frequency for bound
    -> Int     -- ^ Frequency for free
    -> [Name]  -- ^ Names in scope
    -> Gen Name
genVar fb ff inScope = fmap fromIntegral $ frequency
    [ (fb, elements (0:inScope))
    , (ff, return $ notIn inScope)
    ]

genExp :: Int -> [Name] -> Gen (ASTF Dom Int)
genExp s inScope = frequency
    [ (1, fmap int arbitrary)
    , (1, fmap varr $ genVar 1 1 inScope)
    , (s, do a <- genExp (s-1) inScope
             return $ neg a
      )
    , (s, do a <- genExp (s `div` 2) inScope
             b <- genExp (s `div` 2) inScope
             return $ add a b
      )
    , (s, do f <- genExp1 (s `div` 2) inScope
             a <- genExp (s `div` 2) inScope
             return $ app1 f a
      )
    , (s, do f <- genExp2 (s `div` 3) inScope
             a <- genExp (s `div` 3) inScope
             b <- genExp (s `div` 3) inScope
             return $ app2 f a b
      )
    , (s, do f <- genExp3 (s `div` 4) inScope
             a <- genExp (s `div` 4) inScope
             b <- genExp (s `div` 4) inScope
             c <- genExp (s `div` 4) inScope
             return $ app3 f a b c
      )
    ]

genExp1 :: Int -> [Name] -> Gen (ASTF Dom (Int -> Int))
genExp1 s inScope = do
    v    <- genVar 1 2 inScope
    body <- genExp (s-1) (v:inScope)
    return $ lamm v body

genExp2 :: Int -> [Name] -> Gen (ASTF Dom (Int -> Int -> Int))
genExp2 s inScope = do
    v1   <- genVar 1 2 inScope
    v2   <- genVar 1 2 (v1:inScope)
    body <- genExp (s-2) (v2:v1:inScope)
    return $ lamm v1 $ lamm v2 body

genExp3 :: Int -> [Name] -> Gen (ASTF Dom (Int -> Int -> Int -> Int))
genExp3 s inScope = do
    v1   <- genVar 1 2 inScope
    v2   <- genVar 1 2 (v1:inScope)
    v3   <- genVar 1 2 (v2:v1:inScope)
    body <- genExp (s-3) (v3:v2:v1:inScope)
    return $ lamm v1 $ lamm v2 $ lamm v3 body

shrinkExp :: AST Dom sig -> [AST Dom sig]
shrinkExp s
    | Just (Int i) <- prj s = map int $ shrink i
shrinkExp (Sym (Typed lam) :$ body)
    | Just (LamT v) <- prj lam = [sugarSymTyped (LamT v) b | b <- shrinkExp body]
shrinkExp (app1 :$ f :$ a)
    | Just App1 <- prj app1 = concat
        [ case f of
            lam :$ body | Just (LamT _) <- prj lam -> [body]
            _ -> []
        , [a]
        , [ sugarSymTyped App1 f' a' | (f',a') <- shrink (f,a) ]
        ]
shrinkExp (app2 :$ f :$ a :$ b)
    | Just App2 <- prj app2 = concat
        [ case f of
            lam1 :$ (lam2 :$ body)
                | Just (LamT _) <- prj lam1
                , Just (LamT _) <- prj lam2
                -> [body]
            _ -> []
        , [a,b]
        , [ sugarSymTyped App2 f' a' b' | (f',a',b') <- shrink (f,a,b) ]
        ]
shrinkExp (app3 :$ f :$ a :$ b :$ c)
    | Just App3 <- prj app3 = concat
        [ case f of
            lam1 :$ (lam2 :$ (lam3 :$ body))
                | Just (LamT _) <- prj lam1
                , Just (LamT _) <- prj lam2
                , Just (LamT _) <- prj lam3
                -> [body]
            _ -> []
        , [a,b,c]
        , [ sugarSymTyped App3 f' a' b' c' | (f',a',b',c') <- shrink (f,a,b,c) ]
        ]
shrinkExp _ = []

instance Arbitrary (Exp Int)
  where
    arbitrary = sized $ \s -> genExp s []
    shrink = shrinkExp

instance Arbitrary (Exp (Int -> Int))
  where
    arbitrary = sized $ \s -> genExp1 s []
    shrink = shrinkExp

instance Arbitrary (Exp (Int -> Int -> Int))
  where
    arbitrary = sized $ \s -> genExp2 s []
    shrink = shrinkExp

instance Arbitrary (Exp (Int -> Int -> Int -> Int))
  where
    arbitrary = sized $ \s -> genExp3 s []
    shrink = shrinkExp

prop_freeVars (a :: Exp Int) = freeVars a `Set.isSubsetOf` allVars a

prop_alphaEq_refl (a :: Exp Int) = alphaEq a a

prop_alphaEq_rename (a :: Exp Int) = alphaEq a (renameUnique a)

evalAny :: Exp Int -> Int
evalAny a = evalOpen env a
  where
    fv  = freeVars a
    env = zip (Set.toList fv) (map toDyn [(100 :: Int), 110 ..])

prop_renameUnique_vars (a :: Exp Int) = freeVars a == freeVars (renameUnique a)
prop_renameUnique_eval (a :: Exp Int) = evalAny a == evalAny (renameUnique a)

cm :: Exp a -> Exp a
cm = codeMotion $ defaultInterface VarT LamT (\_ _ -> True) (\_ -> True)

prop_codeMotion_vars (a :: Exp Int) = freeVars a == freeVars (cm a)
prop_codeMotion_eval (a :: Exp Int) = evalAny a == evalAny (cm a)

prop_bug1 = prop_codeMotion_eval exp
  where
    exp = add
        (app2 (lamm 0 (lamm 0 (varr 1))) (int 0) (int 0))
        (app2 (lamm 1 (lamm 2 (varr 1))) (int 0) (int 0))


tests = $testGroupGenerator

