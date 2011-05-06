-- | Literal expressions

module Language.Syntactic.Features.Literal where



import Data.Typeable

import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash



data Literal a
  where
    Literal :: (Eq a, Show a, Typeable a) => a -> Literal (Full a)

instance ExprEq Literal
  where
    Literal a `exprEq` Literal b = case cast a of
        Just a' -> a'==b
        Nothing -> False

instance Render Literal
  where
    render (Literal a) = show a

instance ToTree Literal

instance Eval Literal
  where
    evaluate (Literal a) = consEval a

instance ExprHash Literal
  where
    exprHash (Literal a) = hash (show a)



lit :: (Eq a, Show a, Typeable a, Literal :<: expr) => a -> ASTF expr a
lit = inject . Literal

