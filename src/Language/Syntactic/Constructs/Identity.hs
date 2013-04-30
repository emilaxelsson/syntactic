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
    type Sat Identity = Top
    exprDict _ = Dict

instance Semantic Identity
  where
    semantics Id = Sem "id" id

semanticInstances ''Identity

