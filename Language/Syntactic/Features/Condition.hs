-- | Conditional expressions

module Language.Syntactic.Features.Condition where



import Data.Hash

import Language.Syntactic.Syntax
import Language.Syntactic.Analysis.Equality
import Language.Syntactic.Analysis.Render
import Language.Syntactic.Analysis.Evaluation
import Language.Syntactic.Analysis.Hash



data Condition a
  where
    Condition :: Condition (Bool :-> a :-> a :-> Full a)

instance ExprEq Condition
  where
    exprEq Condition Condition = True

instance Render Condition
  where
    render Condition = "condition"

instance ToTree Condition

instance Eval Condition
  where
    evaluate Condition = consEval $
        \cond tHEN eLSE -> if cond then tHEN else eLSE

instance ExprHash Condition
  where
    exprHash Condition = hashInt 0



condition :: (Condition :<: dom, Syntactic a dom) =>
    ASTF dom Bool -> a -> a -> a
condition cond tHEN eLSE = sugar $ inject Condition
    :$: cond
    :$: desugar tHEN
    :$: desugar eLSE

