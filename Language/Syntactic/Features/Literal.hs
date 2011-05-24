-- | Literal expressions

module Language.Syntactic.Features.Literal where



import Data.Typeable

import Data.Hash

import Language.Syntactic



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
    evaluate (Literal a) = fromEval a

instance ExprHash Literal
  where
    exprHash (Literal a) = hash (show a)



-- | Literal
lit :: (Eq a, Show a, Typeable a, Literal :<: dom) => a -> ASTF dom a
lit = inject . Literal

-- | Annotated literal
litAnn :: (Eq a, Show a, Typeable a, Literal :<: dom) =>
    info a -> a -> AnnSTF info dom a
litAnn info = injectAnn info . Literal

