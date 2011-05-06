module Language.Syntactic.Analysis.Evaluation where



import Language.Syntactic.Syntax



class Eval expr
  where
    -- | Evaluation of expressions
    evaluate :: expr a -> a

instance Eval expr => Eval (AST expr)
  where
    evaluate (Symbol a) = evaluate a
    evaluate (f :$: a)  = evaluate f $: result (evaluate a)

instance (Eval expr1, Eval expr2) => Eval (expr1 :+: expr2)
  where
    evaluate (InjectL a) = evaluate a
    evaluate (InjectR a) = evaluate a

evalFull :: Eval expr => ASTF expr a -> a
evalFull = result . evaluate

evalSyn :: (Syntactic a dom, Eval dom) => a -> Internal a
evalSyn = evalFull . desugar

