{-# LANGUAGE TemplateHaskell #-}

-- | Default implementations of some interpretation functions

module Language.Syntactic.Interpretation.Semantics where



import Language.Syntactic.Syntax


-- | A representation of a syntactic construct as a 'String' and an evaluation
-- function. It is not meant to be used as a syntactic symbol in an 'AST'. Its
-- only purpose is to provide the default implementations of functions like
-- `equal` via the `Semantic` class.
data Semantics a
  where
    Sem
        :: { semanticName :: String
           , semanticEval :: Denotation a
           }
        -> Semantics a


-- | The denotation of a symbol with the given signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig


-- | Class of expressions that can be treated as constructs
class Semantic expr
  where
    semantics :: expr a -> Semantics a
