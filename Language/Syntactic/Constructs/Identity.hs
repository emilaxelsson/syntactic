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

instance Equality Identity where equal = equalDefault; exprHash = exprHashDefault
instance Render   Identity where renderArgs = renderArgsDefault
instance Eval     Identity where evaluate   = evaluateDefault
instance ToTree   Identity

