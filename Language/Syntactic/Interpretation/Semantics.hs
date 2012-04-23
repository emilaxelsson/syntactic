-- | Default implementations of some interpretation functions

module Language.Syntactic.Interpretation.Semantics where



import Data.Typeable

import Data.Hash
import Data.Proxy

import Language.Syntactic.Syntax
import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Render
import Language.Syntactic.Interpretation.Evaluation



-- | A representation of a syntactic construct as a 'String' and an evaluation
-- function. It is not meant to be used as a syntactic symbol in an 'AST'. Its
-- only purpose is to provide the default implementations of functions like
-- `exprEq` via the `Semantic` class.
data Semantics a
  where
    Sem :: Signature a
        => { semanticName :: String
           , semanticEval :: Denotation a
           }
        -> Semantics a



instance ExprEq Semantics
  where
    exprEq (Sem a _) (Sem b _) = a==b
    exprHash (Sem name _)      = hash name

instance Render Semantics
  where
    renderPart [] (Sem name _) = name
    renderPart args (Sem name _)
        | isInfix   = "(" ++ unwords [a,op,b] ++ ")"
        | otherwise = "(" ++ unwords (name : args) ++ ")"
      where
        [a,b] = args
        op    = init $ tail name
        isInfix
          =  not (null name)
          && head name == '('
          && last name == ')'
          && length args == 2

instance Eval Semantics
  where
    evaluate (Sem _ a) = fromEval a



-- | Class of expressions that can be treated as constructs
class Semantic expr
  where
    semantics :: expr a -> Semantics a

-- | Default implementation of 'exprEq'
exprEqSem :: Semantic expr => expr a -> expr b -> Bool
exprEqSem a b = exprEq (semantics a) (semantics b)

-- | Default implementation of 'exprHash'
exprHashSem :: Semantic expr => expr a -> Hash
exprHashSem = exprHash . semantics

-- | Default implementation of 'renderPart'
renderPartSem :: Semantic expr => [String] -> expr a -> String
renderPartSem args = renderPart args . semantics

-- | Default implementation of 'evaluate'
evaluateSem :: Semantic expr => expr a -> a
evaluateSem = evaluate . semantics

