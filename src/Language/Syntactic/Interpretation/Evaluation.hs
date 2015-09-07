{-# LANGUAGE DefaultSignatures #-}

module Language.Syntactic.Interpretation.Evaluation where



import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Semantics



class Eval expr
  where
    -- | Evaluation of expressions
    evaluate :: expr a -> Denotation a

    default evaluate :: Semantic expr => expr a -> Denotation a
    evaluate = evaluateDefault
    {-# INLINABLE evaluate #-}

-- | Default implementation of 'evaluate'
evaluateDefault :: Semantic expr => expr a -> Denotation a
evaluateDefault = evaluate . semantics
{-# INLINE evaluateDefault #-}

instance Eval Semantics
  where
    {-# SPECIALIZE instance Eval Semantics #-}
    {-# INLINABLE evaluate #-}
    evaluate (Sem _ a) = a


instance Eval dom => Eval (AST dom)
  where
    {-# SPECIALIZE instance (Eval dom) => Eval (AST dom) #-}
    {-# INLINABLE evaluate #-}
    evaluate (Sym a)  = evaluate a
    evaluate (s :$ a) = evaluate s $ evaluate a

instance (Eval expr1, Eval expr2) => Eval (expr1 :+: expr2)
  where
    {-# SPECIALIZE instance (Eval expr1, Eval expr2) => Eval (expr1 :+: expr2) #-}
    {-# INLINABLE evaluate #-}
    evaluate (InjL a) = evaluate a
    evaluate (InjR a) = evaluate a
