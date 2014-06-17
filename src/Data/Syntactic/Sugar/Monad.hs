{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for 'Remon' using 'Binding' to handle variable binding

module Data.Syntactic.Sugar.Monad where



import Control.Monad.Cont

import Data.Syntactic
import Data.Syntactic.Functional
import Data.Syntactic.Sugar.Binding



-- | One-layer sugaring of monadic actions
sugarMonad :: (Binding :<: sym) => ASTF sym (m a) -> Remon sym m (ASTF sym a)
sugarMonad ma = Remon $ cont $ sugarSym Bind ma

instance
    ( Syntactic a
    , Domain a ~ sym
    , Binding :<: sym
    , MONAD m :<: sym
    , Monad m
    ) =>
      Syntactic (Remon sym m a)
  where
    type Domain (Remon sym m a)   = sym
    type Internal (Remon sym m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

