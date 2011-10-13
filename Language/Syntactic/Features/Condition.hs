{-# LANGUAGE OverlappingInstances #-}

-- | Conditional expressions

module Language.Syntactic.Features.Condition where



import Data.Hash
import Data.Proxy
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Features.Symbol



data Condition ctx a
  where
    Condition :: Sat ctx a => Condition ctx (Bool :-> a :-> a :-> Full a)

instance WitnessCons (Condition ctx)
  where
    witnessCons Condition = ConsWit

instance WitnessSat (Condition ctx)
  where
    type SatContext (Condition ctx) = ctx
    witnessSat Condition = SatWit

instance MaybeWitnessSat ctx (Condition ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Condition ctx2)
  where
    maybeWitnessSat _ _ = Nothing

instance IsSymbol (Condition ctx)
  where
    toSym Condition = Sym "condition" (\c t e -> if c then t else e)

instance ExprEq (Condition ctx) where exprEq = exprEqSym; exprHash = exprHashSym
instance Render (Condition ctx) where renderPart = renderPartSym
instance Eval   (Condition ctx) where evaluate   = evaluateSym
instance ToTree (Condition ctx)

