{-# LANGUAGE UndecidableInstances #-}

-- | 'Syntactic' instance for functions
--
-- This module is based on having 'BindingT' in the domain. For 'Binding' import module
-- "Data.Syntactic.Sugar.Binding" instead

module Data.Syntactic.Sugar.BindingT where



import Data.Syntactic
import Data.Syntactic.TypeUniverse
import Data.Syntactic.Functional



-- | The type universe for variables
type family VarUniverse (dom :: * -> *) :: * -> *

type instance VarUniverse (BindingT t) = t
type instance VarUniverse (BindingT t :+: dom) = t

type instance VarUniverse Construct = Empty
type instance VarUniverse (Construct :+: dom) = VarUniverse dom
  -- TODO With closed type families, this instance could be avoided.

instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , t ~ VarUniverse dom
    , BindingT t :<: dom
    , Typeable t (Internal a)
    ) =>
      Syntactic (a -> b)
  where
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lamT (Proxy :: Proxy t) (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"

