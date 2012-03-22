{-# LANGUAGE OverlappingInstances #-}

-- | Provides a simple way to make syntactic constructs for prototyping. Note
-- that 'Construct' is quite unsafe as it only uses 'String' to distinguish
-- between different constructs. Also, 'Construct' has a very free type that
-- allows any number of arguments.

module Language.Syntactic.Constructs.Construct where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic



data Construct ctx a
  where
    Construct :: (Signature a, Sat ctx (DenResult a)) =>
        String -> Denotation a -> Construct ctx a

instance WitnessCons (Construct ctx)
  where
    witnessCons (Construct _ _) = ConsWit

instance WitnessSat (Construct ctx)
  where
    type SatContext (Construct ctx) = ctx
    witnessSat (Construct _ _) = SatWit

instance MaybeWitnessSat ctx (Construct ctx)
  where
    maybeWitnessSat = maybeWitnessSatDefault

instance MaybeWitnessSat ctx1 (Construct ctx2)
  where
    maybeWitnessSat _ _ = Nothing

instance ExprEq (Construct ctx)
  where
    exprEq (Construct a _) (Construct b _) = a==b
    exprHash (Construct name _)            = hash name

instance Render (Construct ctx)
  where
    renderPart [] (Construct name _) = name
    renderPart args (Construct name _)
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

instance ToTree (Construct ctx)

instance Eval (Construct ctx)
  where
    evaluate (Construct _ a) = fromEval a

