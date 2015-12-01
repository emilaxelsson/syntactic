{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for functions for domains based on 'Binding'

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

