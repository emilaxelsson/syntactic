-- | Conditional expressions

module Language.Syntactic.Features.Condition where



import Data.Hash
import Data.Proxy

import Language.Syntactic



data Condition ctx a
  where
    Condition :: Sat ctx a =>
        Proxy ctx -> Condition ctx (Bool :-> a :-> a :-> Full a)

instance WitnessCons (Condition ctx)
  where
    witnessCons (Condition _) = ConsWit

instance ExprEq (Condition ctx)
  where
    exprEq (Condition _) (Condition _) = True

instance Render (Condition ctx)
  where
    render (Condition _) = "condition"

instance ToTree (Condition ctx)

instance Eval (Condition ctx)
  where
    evaluate (Condition _) = fromEval $
        \cond tHEN eLSE -> if cond then tHEN else eLSE

instance ExprHash (Condition ctx)
  where
    exprHash (Condition _) = hashInt 0



-- | Conditional expression with explicit context
conditionCtx
    :: (Sat ctx (Internal a), Condition ctx :<: dom, Syntactic a dom)
    => Proxy ctx -> ASTF dom Bool -> a -> a -> a
conditionCtx ctx cond tHEN eLSE = sugar $ inject (Condition ctx)
    :$: cond
    :$: desugar tHEN
    :$: desugar eLSE

-- | Conditional expression
condition :: (Condition Poly :<: dom, Syntactic a dom) =>
    ASTF dom Bool -> a -> a -> a
condition = conditionCtx poly



-- | Partial `Condition` projection with explicit context
prjCondition :: (Condition ctx :<: sup) =>
    Proxy ctx -> sup a -> Maybe (Condition ctx a)
prjCondition _ = project

