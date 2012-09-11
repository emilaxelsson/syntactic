-- | Provides a simple way to make syntactic constructs for prototyping. Note
-- that 'Construct' is quite unsafe as it only uses 'String' to distinguish
-- between different constructs. Also, 'Construct' has a very free type that
-- allows any number of arguments.

module Language.Syntactic.Constructs.Construct where



import Language.Syntactic



data Construct sig
  where
    Construct :: String -> Denotation sig -> Construct sig

instance Constrained Construct
  where
    type Sat Construct = Top
    exprDict _ = Dict

instance Semantic Construct
  where
    semantics (Construct name den) = Sem name den

instance Equality Construct where equal = equalDefault; exprHash = exprHashDefault
instance Render   Construct where renderArgs = renderArgsDefault
instance Eval     Construct where evaluate   = evaluateDefault
instance ToTree   Construct

