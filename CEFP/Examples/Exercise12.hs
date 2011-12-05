{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol

import MuFeldspar.Core



data ForLoop' a
  where
    ForLoop' :: Type st =>
        ForLoop' (Length :-> st :-> (Index -> st -> st) :-> Full st)

instance IsSymbol ForLoop'
  where
    toSym ForLoop' = Sym "forLoop" forLoop
      where
        forLoop len init body = foldl (flip body) init (reverse [0 .. len-1])

instance ExprEq ForLoop' where exprEq     = exprEqSym
instance Render ForLoop' where renderPart = renderPartSym
instance Eval   ForLoop' where evaluate   = evaluateSym
instance ToTree ForLoop'

