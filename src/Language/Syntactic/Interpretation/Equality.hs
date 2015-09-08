{-# LANGUAGE DefaultSignatures #-}

module Language.Syntactic.Interpretation.Equality where



import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Semantics



-- | Equality for expressions
class Equality expr
  where
    -- | Equality for expressions
    --
    -- Comparing expressions of different types is often needed when dealing
    -- with expressions with existentially quantified sub-terms.
    equal :: expr a -> expr b -> Bool

    -- | Computes a 'Hash' for an expression. Expressions that are equal
    -- according to 'equal' must result in the same hash:
    --
    -- @equal a b  ==>  exprHash a == exprHash b@
    exprHash :: expr a -> Hash

    default equal :: Semantic expr => expr a -> expr b -> Bool
    equal = equalDefault
    {-# INLINABLE equal #-}

    default exprHash :: Semantic expr => expr a -> Hash
    exprHash = exprHashDefault
    {-# INLINABLE exprHash #-}


-- | Default implementation of 'equal'
equalDefault :: Semantic expr => expr a -> expr b -> Bool
equalDefault a b = equal (semantics a) (semantics b)
{-# INLINE equalDefault #-}

-- | Default implementation of 'exprHash'
exprHashDefault :: Semantic expr => expr a -> Hash
exprHashDefault = exprHash . semantics
{-# INLINE exprHashDefault #-}


instance Equality Semantics
  where
    {-# SPECIALIZE instance Equality Semantics #-}
    {-# INLINABLE equal #-}
    {-# INLINABLE exprHash #-}
    equal (Sem a _) (Sem b _) = a==b
    exprHash (Sem name _)     = hash name

instance Equality dom => Equality (AST dom)
  where
    {-# SPECIALIZE instance (Equality dom) => Equality (AST dom) #-}
    {-# INLINABLE equal #-}
    equal (Sym a)    (Sym b)    = equal a b
    equal (s1 :$ a1) (s2 :$ a2) = equal s1 s2 && equal a1 a2
    equal _ _                   = False

    {-# INLINABLE exprHash #-}
    exprHash (Sym a)  = hashInt 0 `combine` exprHash a
    exprHash (s :$ a) = hashInt 1 `combine` exprHash s `combine` exprHash a

instance Equality dom => Eq (AST dom a)
  where
    {-# SPECIALIZE instance (Equality dom) => Eq (AST dom a) #-}
    {-# INLINABLE (==) #-}
    (==) = equal

instance (Equality expr1, Equality expr2) => Equality (expr1 :+: expr2)
  where
    {-# SPECIALIZE instance (Equality expr1, Equality expr2) => Equality (expr1 :+: expr2) #-}
    {-# INLINABLE equal #-}
    equal (InjL a) (InjL b) = equal a b
    equal (InjR a) (InjR b) = equal a b
    equal _ _               = False

    {-# INLINABLE exprHash #-}
    exprHash (InjL a) = hashInt 0 `combine` exprHash a
    exprHash (InjR a) = hashInt 1 `combine` exprHash a

instance (Equality expr1, Equality expr2) => Eq ((expr1 :+: expr2) a)
  where
    {-# SPECIALIZE instance (Equality expr1, Equality expr2) => Eq ((expr1 :+: expr2) a)#-}
    (==) = equal
