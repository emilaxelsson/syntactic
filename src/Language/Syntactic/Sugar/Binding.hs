{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for functions
--
-- This module is based on having 'Binding' in the domain. For 'BindingT' import
-- module "Language.Syntactic.Sugar.BindingT" instead.

module Language.Syntactic.Sugar.Binding where



import Language.Syntactic
import Language.Syntactic.Functional



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

