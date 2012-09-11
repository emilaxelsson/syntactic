module Language.Syntactic.Interpretation.Evaluation where



import Language.Syntactic.Syntax



-- | The denotation of a symbol with the given signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

class Eval expr
  where
    -- | Evaluation of expressions
    evaluate :: expr a -> Denotation a

instance Eval dom => Eval (AST dom)
  where
    evaluate (Sym a)  = evaluate a
    evaluate (s :$ a) = evaluate s $ evaluate a

instance (Eval expr1, Eval expr2) => Eval (expr1 :+: expr2)
  where
    evaluate (InjL a) = evaluate a
    evaluate (InjR a) = evaluate a

