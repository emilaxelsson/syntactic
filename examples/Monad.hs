{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-missing-methods #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module demonstrates monad reification.
-- See \"Generic Monadic Constructs for Embedded Languages\" (Persson et al., IFL 2011
-- <https://emilaxelsson.github.io/documents/persson2011generic.pdf>) for details.

module Monad where



import Control.Monad (replicateM_)
import Data.Char (isDigit)
import Data.Typeable (Typeable)

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Sugar.MonadTyped ()

import NanoFeldspar (Type, Arithmetic (..))



type Dom = Typed (BindingT :+: MONAD IO :+: Construct :+: Arithmetic)

type Exp a = ASTF Dom a

type IO' a = Remon Dom IO (Exp a)

getDigit :: IO' Int
getDigit = sugarSymTyped $ Construct "getDigit" get
  where
    get = do
        c <- getChar
        if isDigit c then return (fromEnum c - fromEnum '0') else get

putDigit :: Exp Int -> IO' ()
putDigit = sugarSymTyped $ Construct "putDigit" print

iter :: Typeable a => Exp Int -> IO' a -> IO' ()
iter = sugarSymTyped $ Construct "iter" replicateM_

-- | Literal
value :: (Show a, Typeable a) => a -> Exp a
value a = sugarSymTyped $ Construct (show a) a

instance (Num a, Type a) => Num (Exp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSymTyped Add
    (-)         = sugarSymTyped Sub
    (*)         = sugarSymTyped Mul

ex1 :: Exp Int -> IO' ()
ex1 n = iter n $ do
    d <- getDigit
    putDigit (d+d)

test1 = evalClosed (desugar ex1) 5
test2 = drawAST $ desugar ex1

