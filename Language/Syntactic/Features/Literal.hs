-- | Literal expressions

module Language.Syntactic.Features.Literal where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic



data Literal ctx a
  where
    Literal :: (Eq a, Show a, Typeable a, Sat ctx a) =>
        Proxy ctx -> a -> Literal ctx (Full a)

instance WitnessCons (Literal ctx)
  where
    witnessCons (Literal _ _) = ConsWit

instance ExprEq (Literal ctx)
  where
    Literal _ a `exprEq` Literal _ b = case cast a of
        Just a' -> a'==b
        Nothing -> False

instance Render (Literal ctx)
  where
    render (Literal _ a) = show a

instance ToTree (Literal ctx)

instance Eval (Literal ctx)
  where
    evaluate (Literal _ a) = fromEval a

instance ExprHash (Literal ctx)
  where
    exprHash (Literal _ a) = hash (show a)



-- | Literal with explicit context
litCtx :: (Eq a, Show a, Typeable a, Sat ctx a, Literal ctx :<: dom) =>
    Proxy ctx -> a -> ASTF dom a
litCtx ctx = inject . Literal ctx

-- | Literal
lit :: (Eq a, Show a, Typeable a, Literal Poly :<: dom) => a -> ASTF dom a
lit = litCtx poly

-- | Partial literal projection with explicit context
prjLiteral :: (Literal ctx :<: sup) =>
    Proxy ctx -> sup a -> Maybe (Literal ctx a)
prjLiteral _ = project

