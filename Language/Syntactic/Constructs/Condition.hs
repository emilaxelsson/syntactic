{-# LANGUAGE OverlappingInstances #-}

-- | Conditional expressions

module Language.Syntactic.Constructs.Condition where



import Data.Proxy
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Interpretation.Semantics



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

instance Semantic (Condition ctx)
  where
    semantics Condition = Sem "condition" (\c t e -> if c then t else e)

instance ExprEq (Condition ctx) where exprEq = exprEqSem; exprHash = exprHashSem
instance Render (Condition ctx) where renderPart = renderPartSem
instance Eval   (Condition ctx) where evaluate   = evaluateSem
instance ToTree (Condition ctx)

