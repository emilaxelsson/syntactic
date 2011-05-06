module Language.Syntactic.Analysis.Hash where



import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality



class ExprEq expr => ExprHash expr
  where
    -- | Computes a 'Hash' for an expression. Expressions that are equal
    -- according to 'exprEq' must result in the same hash.
    exprHash :: expr a -> Hash

instance ExprHash expr => ExprHash (AST expr)
  where
    exprHash (Symbol a) = hashInt 0 `combine` exprHash a
    exprHash (f :$: a)  = hashInt 1 `combine` exprHash f `combine` exprHash a

instance (ExprHash expr1, ExprHash expr2) => ExprHash (expr1 :+: expr2)
  where
    exprHash (InjectL a) = hashInt 0 `combine` exprHash a
    exprHash (InjectR a) = hashInt 1 `combine` exprHash a

