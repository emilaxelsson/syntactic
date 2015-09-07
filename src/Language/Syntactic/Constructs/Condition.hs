{-# LANGUAGE TemplateHaskell #-}

-- | Conditional expressions

module Language.Syntactic.Constructs.Condition where



import Language.Syntactic



data Condition sig
  where
    Condition :: Condition (Bool :-> a :-> a :-> Full a)

instance Constrained Condition
  where
    {-# SPECIALIZE instance Constrained Condition #-}
    {-# INLINABLE exprDict #-}
    type Sat Condition = Top
    exprDict = const Dict

instance Semantic Condition
  where
    {-# SPECIALIZE instance Semantic Condition #-}
    {-# INLINABLE semantics #-}
    semantics Condition = Sem "condition" (\c t e -> if c then t else e)

semanticInstances ''Condition
