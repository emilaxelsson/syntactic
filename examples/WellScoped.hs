{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -fno-warn-missing-methods #-}

-- | This module demonstrates the use of 'WS' terms. In particular, note that 'share' has no
-- constraints on the type @a@ in contrast to the corresponding function in NanoFeldspar.
--
-- 'WS' terms can be evaluated directly using 'evalClosedWS' and they can be examined by first
-- converting them using the function 'fromWS'.

module WellScoped where



import Data.Proxy

import Data.Syntactic
import Data.Syntactic.Functional

import NanoFeldspar (Arithmetic (..), Let (..))



type Exp e a = WS (Let :+: Construct) e a

instance (Num a, Show a) => Num (Exp e a)
  where
    fromInteger i = smartWS Proxy $ Construct (show i') i'
      where i' = fromInteger i
    (+) = smartWS Proxy $ Construct "(+)" (+)

share :: forall e a b .
    Exp e a -> ((forall e' . Ext e' (a,e) => Exp e' a) -> Exp (a,e) b) -> Exp e b
share a f = smartWS Proxy Let a $ lamWS f

ex1 :: Exp e (Int -> Int)
ex1 = lamWS $ \a -> share (a + 4) $ \b -> share (a+b) $ \c -> a+b+c

test1 = evalClosedWS ex1 5
test2 = drawAST $ fromWS ex1

