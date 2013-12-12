module Data.Syntactic.Interpretation.Equality where



import Data.Hash

import Data.Syntactic.Syntax



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


instance Equality sym => Equality (AST sym)
  where
    equal (Sym s1)   (Sym s2)   = equal s1 s2
    equal (s1 :$ a1) (s2 :$ a2) = equal s1 s2 && equal a1 a2
    equal _ _                   = False

    exprHash (Sym s)  = hashInt 0 `combine` exprHash s
    exprHash (s :$ a) = hashInt 1 `combine` exprHash s `combine` exprHash a

instance Equality sym => Eq (AST sym a)
  where
    (==) = equal

instance (Equality sym1, Equality sym2) => Equality (sym1 :+: sym2)
  where
    equal (InjL a) (InjL b) = equal a b
    equal (InjR a) (InjR b) = equal a b
    equal _ _               = False

    exprHash (InjL a) = hashInt 0 `combine` exprHash a
    exprHash (InjR a) = hashInt 1 `combine` exprHash a

instance (Equality expr1, Equality expr2) => Eq ((expr1 :+: expr2) a)
  where
    (==) = equal

