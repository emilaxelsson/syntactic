module Language.Syntactic.Interpretation.Equality where



import Data.Hash

import Language.Syntactic.Syntax



-- | Equality for expressions. The difference between 'Eq' and 'ExprEq' is that
-- 'ExprEq' allows comparison of expressions with different value types. It is
-- assumed that when the types differ, the expressions also differ. The reason
-- for allowing comparison of different types is that this is convenient when
-- the types are existentially quantified.
class ExprEq expr
  where
    exprEq :: expr a -> expr b -> Bool

    -- | Computes a 'Hash' for an expression. Expressions that are equal
    -- according to 'exprEq' must result in the same hash:
    --
    -- @`exprEq` a b  ==>  `exprHash` a == `exprHash` b@
    exprHash :: expr a -> Hash


instance ExprEq dom => ExprEq (AST dom)
  where
    exprEq (Sym a)    (Sym b)    = exprEq a b
    exprEq (f1 :$ a1) (f2 :$ a2) = exprEq f1 f2 && exprEq a1 a2
    exprEq _ _ = False

    exprHash (Sym a)  = hashInt 0 `combine` exprHash a
    exprHash (f :$ a) = hashInt 1 `combine` exprHash f `combine` exprHash a

instance ExprEq dom => Eq (AST dom a)
  where
    (==) = exprEq

instance (ExprEq expr1, ExprEq expr2) => ExprEq (expr1 :+: expr2)
  where
    exprEq (InjL a) (InjL b) = exprEq a b
    exprEq (InjR a) (InjR b) = exprEq a b
    exprEq _ _ = False

    exprHash (InjL a) = hashInt 0 `combine` exprHash a
    exprHash (InjR a) = hashInt 1 `combine` exprHash a

instance (ExprEq expr1, ExprEq expr2) => Eq ((expr1 :+: expr2) a)
  where
    (==) = exprEq

