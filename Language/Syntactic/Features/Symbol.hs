{-# LANGUAGE OverlappingInstances #-}

-- | Generic symbols
--
-- 'Sym' provides a simple way to make syntactic symbols for prototyping.
-- However, note that 'Sym' is quite unsafe as it only uses 'String' to
-- distinguish between different symbols. Also, 'Sym' has a very free type that
-- allows any number of arguments.

module Language.Syntactic.Features.Symbol where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic



data Sym ctx a
  where
    Sym :: (ConsType a, Sat ctx (EvalResult a)) =>
        String -> ConsEval a -> Sym ctx a

instance WitnessCons (Sym ctx)
  where
    witnessCons (Sym _ _) = ConsWit

instance WitnessSat (Sym ctx)
  where
    type SatContext (Sym ctx) = ctx
    witnessSat (Sym _ _) = SatWit

instance MaybeWitnessSat ctx (Sym ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Sym ctx2)
  where
    maybeWitnessSat _ _ = Nothing

instance ExprEq (Sym ctx)
  where
    exprEq (Sym a _) (Sym b _) = a==b
    exprHash (Sym name _)      = hash name

instance Render (Sym ctx)
  where
    renderPart [] (Sym name _) = name
    renderPart args (Sym name _)
        | isInfix   = "(" ++ unwords [a,op,b] ++ ")"
        | otherwise = "(" ++ unwords (name : args) ++ ")"
      where
        [a,b] = args
        op    = init $ tail name
        isInfix
          =  not (null name)
          && head name == '('
          && last name == ')'
          && length args == 2

instance ToTree (Sym ctx)

instance Eval (Sym ctx)
  where
    evaluate (Sym _ a) = fromEval a



-- | Class of expressions that can be treated as symbols
class IsSymbol expr
  where
    toSym :: expr a -> Sym Poly a

-- | Default implementation of 'exprEq'
exprEqSym :: IsSymbol expr => expr a -> expr b -> Bool
exprEqSym a b = exprEq (toSym a) (toSym b)

-- | Default implementation of 'exprHash'
exprHashSym :: IsSymbol expr => expr a -> Hash
exprHashSym = exprHash . toSym

-- | Default implementation of 'renderPart'
renderPartSym :: IsSymbol expr => [String] -> expr a -> String
renderPartSym args = renderPart args . toSym

-- | Default implementation of 'evaluate'
evaluateSym :: IsSymbol expr => expr a -> a
evaluateSym = evaluate . toSym

