{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

-- | This module demonstrates monad reification.
-- See \"Generic Monadic Constructs for Embedded Languages\" (Persson et al., IFL 2011
-- <http://www.cse.chalmers.se/~emax/documents/persson2011generic.pdf>) for details.

module Monad where



import Control.Monad (replicateM_)
import Data.Char (isDigit)
import Data.Typeable (Typeable)

import Data.Syntactic
import Data.Syntactic.Functional
import Data.Syntactic.Sugar.MonadT

import NanoFeldspar (Type, Arithmetic (..))



type Dom = BindingT :+: MONAD IO :+: Construct :+: Arithmetic

type Exp a = ASTF Dom a

type IO' a = Remon Dom IO (Exp a)

getDigit :: IO' Int
getDigit = sugarSym $ Construct "getDigit" get
  where
    get = do
        c <- getChar
        if isDigit c then return (fromEnum c - fromEnum '0') else get

putDigit :: Exp Int -> IO' ()
putDigit = sugarSym $ Construct "putDigit" print

iter :: Typeable a => Exp Int -> IO' a -> IO' ()
iter = sugarSym $ Construct "iter" replicateM_

-- | Literal
value :: Show a => a -> Exp a
value a = sugar $ inj $ Construct (show a) a

instance (Num a, Type a) => Num (Exp a)
  where
    fromInteger = value . fromInteger
    (+)         = sugarSym Add
    (-)         = sugarSym Sub
    (*)         = sugarSym Mul

ex1 :: Exp Int -> IO' ()
ex1 n = iter n $ do
    d <- getDigit
    putDigit (d+d)

test1 = evalClosed (desugar ex1) 5
test2 = drawAST $ desugar ex1

