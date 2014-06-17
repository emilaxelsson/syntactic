{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for 'Mon' using 'BindingT' to handle variable binding

module Data.Syntactic.Sugar.MonadT where



import Control.Monad.Cont
import Data.Typeable

import Data.Syntactic
import Data.Syntactic.Functional
import Data.Syntactic.Sugar.BindingT



-- | One-layer sugaring of monadic actions
sugarMonad :: (BindingT :<: sym, Typeable a) => ASTF sym (m a) -> Mon sym m (ASTF sym a)
sugarMonad ma = Mon $ cont $ sugarSym Bind ma

instance
    ( Syntactic a
    , Domain a ~ sym
    , BindingT :<: sym
    , MONAD m  :<: sym
    , Monad m
    , Typeable (Internal a)
    ) =>
      Syntactic (Mon sym m a)
  where
    type Domain (Mon sym m a)   = sym
    type Internal (Mon sym m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

