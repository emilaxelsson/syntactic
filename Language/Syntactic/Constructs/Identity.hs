{-# LANGUAGE OverlappingInstances #-}

-- | Identity function

module Language.Syntactic.Constructs.Identity where



import Data.Proxy
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Interpretation.Semantics



-- | Identity function
data Identity ctx a
  where
    Id :: Sat ctx a => Identity ctx (a :-> Full a)

instance WitnessCons (Identity ctx)
  where
    witnessCons Id = ConsWit

instance WitnessSat (Identity ctx)
  where
    type SatContext (Identity ctx) = ctx
    witnessSat Id = SatWit

instance MaybeWitnessSat ctx (Identity ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Identity ctx2)
  where
    maybeWitnessSat _ _ = Nothing

instance Semantic (Identity ctx)
  where
    semantics Id = Sem "id" id

instance ExprEq (Identity ctx) where exprEq = exprEqSem; exprHash = exprHashSem
instance Render (Identity ctx) where renderPart = renderPartSem
instance Eval   (Identity ctx) where evaluate   = evaluateSem
instance ToTree (Identity ctx)

