-- | Conditional expressions

module Language.Syntactic.Features.Condition where



import Data.Hash
import Data.Proxy

import Language.Syntactic



data Condition ctx a
  where
    Condition :: Sat ctx a => Condition ctx (Bool :-> a :-> a :-> Full a)

instance WitnessCons (Condition ctx)
  where
    witnessCons Condition = ConsWit

instance WitnessSat (Condition ctx)
  where
    type Context (Condition ctx) = ctx
    witnessSat Condition = Witness'

instance ExprEq (Condition ctx)
  where
    exprEq Condition Condition = True

instance Render (Condition ctx)
  where
    render Condition = "condition"

instance ToTree (Condition ctx)

instance Eval (Condition ctx)
  where
    evaluate Condition = fromEval $
        \cond tHEN eLSE -> if cond then tHEN else eLSE

instance ExprHash (Condition ctx)
  where
    exprHash Condition = hashInt 0



-- | Conditional expression with explicit context
conditionCtx
    :: (Sat ctx (Internal a), Syntactic a dom, Condition ctx :<: dom)
    => Proxy ctx -> ASTF dom Bool -> a -> a -> a
conditionCtx ctx cond tHEN eLSE = sugar $ inject (Condition `withContext` ctx)
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

