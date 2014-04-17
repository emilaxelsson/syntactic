{-# LANGUAGE UndecidableInstances #-}

-- | Syntactic sugar for functions
--
-- This module is based on having 'Binding' in the domain. For 'BindingT' import module
-- "Data.Syntactic.Sugar.BindingT" instead

module Data.Syntactic.Sugar.Binding where



import Data.Syntactic
import Data.Syntactic.Constructs



instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , Binding :<: dom
    ) =>
      Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lam (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"

