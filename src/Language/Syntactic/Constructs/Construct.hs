{-# LANGUAGE TemplateHaskell #-}

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
    {-# SPECIALIZE instance Constrained Construct #-}
    {-# INLINABLE exprDict #-}
    type Sat Construct = Top
    exprDict = const Dict

instance Semantic Construct
  where
    {-# SPECIALIZE instance Semantic Construct #-}
    {-# INLINABLE semantics #-}
    semantics (Construct name den) = Sem name den

semanticInstances ''Construct
