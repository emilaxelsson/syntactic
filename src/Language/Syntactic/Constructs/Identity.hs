{-# LANGUAGE TemplateHaskell #-}

-- | Identity function

module Language.Syntactic.Constructs.Identity where



import Language.Syntactic



-- | Identity function
data Identity sig
  where
    Id :: Identity (a :-> Full a)

instance Constrained Identity
  where
    {-# SPECIALIZE instance Constrained Identity #-}
    {-# INLINABLE exprDict #-}
    type Sat Identity = Top
    exprDict = const Dict

instance Semantic Identity
  where
    {-# SPECIALIZE instance Semantic Identity #-}
    {-# INLINABLE semantics #-}
    semantics Id = Sem "id" id

semanticInstances ''Identity
