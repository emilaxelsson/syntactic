module Language.Syntactic.Interpretation.Evaluation where



import Language.Syntactic.Syntax



class Eval expr
  where
    -- | Evaluation of expressions
    evaluate :: expr a -> a

instance Eval dom => Eval (AST dom)
  where
    evaluate (Sym a)  = evaluate a
    evaluate (f :$ a) = evaluate f $: result (evaluate a)

instance (Eval expr1, Eval expr2) => Eval (expr1 :+: expr2)
  where
    evaluate (InjL a) = evaluate a
    evaluate (InjR a) = evaluate a

evalFull :: Eval dom => ASTF dom a -> a
evalFull = result . evaluate

