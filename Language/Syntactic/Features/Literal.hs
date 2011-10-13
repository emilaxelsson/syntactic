{-# LANGUAGE OverlappingInstances #-}

-- | Literal expressions

module Language.Syntactic.Features.Literal where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic



data Literal ctx a
  where
    Literal :: (Eq a, Show a, Typeable a, Sat ctx a) =>
        a -> Literal ctx (Full a)

instance WitnessCons (Literal ctx)
  where
    witnessCons (Literal _) = ConsWit

instance WitnessSat (Literal ctx)
  where
    type SatContext (Literal ctx) = ctx
    witnessSat (Literal _) = SatWit

instance MaybeWitnessSat ctx (Literal ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Literal ctx2)
  where
    maybeWitnessSat _ _ = Nothing

instance ExprEq (Literal ctx)
  where
    Literal a `exprEq` Literal b = case cast a of
        Just a' -> a'==b
        Nothing -> False

    exprHash (Literal a) = hash (show a)

instance Render (Literal ctx)
  where
    render (Literal a) = show a

instance ToTree (Literal ctx)

instance Eval (Literal ctx)
  where
    evaluate (Literal a) = fromEval a

