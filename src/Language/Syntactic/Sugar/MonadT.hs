{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for 'Remon' using 'BindingT' to handle variable binding

module Language.Syntactic.Sugar.MonadT where



import Control.Monad.Cont
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Sugar.BindingT



-- | One-layer sugaring of monadic actions
sugarMonad :: (BindingT :<: sym, Typeable a) => ASTF sym (m a) -> Remon sym m (ASTF sym a)
sugarMonad ma = Remon $ cont $ sugarSym Bind ma

instance
    ( Syntactic a
    , Domain a ~ sym
    , BindingT :<: sym
    , MONAD m  :<: sym
    , Monad m
    , Typeable (Internal a)
    ) =>
      Syntactic (Remon sym m a)
  where
    type Domain (Remon sym m a)   = sym
    type Internal (Remon sym m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

