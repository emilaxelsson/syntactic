-- | Conditional expressions

module Language.Syntactic.Constructs.Condition where



import Language.Syntactic



data Condition sig
  where
    Condition :: Condition (Bool :-> a :-> a :-> Full a)

instance Constrained Condition
  where
    type Sat Condition = Top
    exprDict _ = Dict

instance Semantic Condition
  where
    semantics Condition = Sem "condition" (\c t e -> if c then t else e)

instance Equality Condition where equal = equalDefault; exprHash = exprHashDefault
instance Render   Condition where renderArgs = renderArgsDefault
instance Eval     Condition where evaluate   = evaluateDefault
instance ToTree   Condition

