{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- TODO Only `InjectC` should be used overlapped. Move to separate module?

-- | Type-constrained syntax trees

module Data.Syntactic.Constraint where



import Data.Typeable

import Data.Constraint
import Data.Proxy

import Data.Syntactic.Syntax
import Data.Syntactic.Interpretation



--------------------------------------------------------------------------------
-- * Existential quantification
--------------------------------------------------------------------------------

-- | Existential quantification
data E e
  where
    E :: e a -> E e

liftE :: (forall a . e a -> b) -> E e -> b
liftE f (E a) = f a

liftE2 :: (forall a b . e a -> e b -> c) -> E e -> E e -> c
liftE2 f (E a) (E b) = f a b

-- | Existential quantification of 'Full'-indexed type
data EF e
  where
    EF :: e (Full a) -> EF e

liftEF :: (forall a . e (Full a) -> b) -> EF e -> b
liftEF f (EF a) = f a

liftEF2 :: (forall a b . e (Full a) -> e (Full b) -> c) -> EF e -> EF e -> c
liftEF2 f (EF a) (EF b) = f a b

-- | Constrained existential quantification of 'Full'-indexed type
data B :: (* -> *) -> (* -> Constraint) -> *
  where
    B :: p a => e (Full a) -> B e p

liftB :: (forall a . p a => e (Full a) -> b) -> B e p -> b
liftB f (B a) = f a

liftB2 :: (forall a b . (p a, p b) => e (Full a) -> e (Full b) -> c) -> B e p -> B e p -> c
liftB2 f (B a) (B b) = f a b



--------------------------------------------------------------------------------
-- * Misc.
--------------------------------------------------------------------------------

universe :: ASTF sym a -> [EF (AST sym)]
universe a = EF a : go a
  where
    go :: AST sym a -> [EF (AST sym)]
    go (Sym s)  = []
    go (s :$ a) = go s ++ universe a

