{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for functions
--
-- This module is based on having 'BindingT' in the domain. For 'Binding' import module
-- "Data.Syntactic.Sugar.Binding" instead

module Data.Syntactic.Sugar.BindingT where



import Data.Typeable

import Data.Syntactic
import Data.Syntactic.Functional



instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , BindingT :<: dom
    , Typeable (Internal a)
    ) =>
      Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lamT (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"

