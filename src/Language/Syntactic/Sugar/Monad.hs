{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for 'Remon' using 'Binding' to handle variable binding

module Language.Syntactic.Sugar.Monad where



import Control.Monad.Cont
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Sugar.Binding ()



-- | One-layer sugaring of monadic actions
sugarMonad :: (Binding :<: sym, MONAD m :<: sym) =>
    ASTF sym (m a) -> Remon sym m (ASTF sym a)
sugarMonad ma = Remon $ cont $ sugarSym Bind ma

instance
    ( Syntactic a
    , Domain a ~ sym
    , Binding :<: sym
    , MONAD m :<: sym
    , Typeable m
    , Typeable (Internal a)
        -- The `Typeable` constraints are only needed due to the `Typeable`
        -- constraint in `Remon`. That constraint, in turn, is only needed by
        -- the module "Language.Syntactic.Sugar.MonadT".
    ) =>
      Syntactic (Remon sym m a)
  where
    type Domain (Remon sym m a)   = sym
    type Internal (Remon sym m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

