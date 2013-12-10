{-# LANGUAGE TemplateHaskell #-}

-- | Default implementations of some interpretation functions

module Data.Syntactic.Interpretation.Semantics where



import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Data.Hash

import Data.Syntactic.Syntax
import Data.Syntactic.Interpretation.Equality
import Data.Syntactic.Interpretation.Render
import Data.Syntactic.Interpretation.Evaluation



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



instance Equality Semantics
  where
    equal (Sem a _) (Sem b _) = a==b
    exprHash (Sem name _)     = hash name

instance Render Semantics
  where
    renderSym (Sem name _) = name
    renderArgs [] (Sem name _) = name
    renderArgs args (Sem name _)
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
    evaluate (Sem _ a) = a



-- | Class of expressions that can be treated as constructs
class Semantic expr
  where
    semantics :: expr a -> Semantics a

-- | Default implementation of 'equal'
equalDefault :: Semantic expr => expr a -> expr b -> Bool
equalDefault a b = equal (semantics a) (semantics b)

-- | Default implementation of 'exprHash'
exprHashDefault :: Semantic expr => expr a -> Hash
exprHashDefault = exprHash . semantics

-- | Default implementation of 'renderSym'
renderSymDefault :: Semantic expr => expr a -> String
renderSymDefault = renderSym . semantics

-- | Default implementation of 'renderArgs'
renderArgsDefault :: Semantic expr => [String] -> expr a -> String
renderArgsDefault args = renderArgs args . semantics

-- | Default implementation of 'evaluate'
evaluateDefault :: Semantic expr => expr a -> Denotation a
evaluateDefault = evaluate . semantics

-- | Derive instances for 'Semantic' related classes
-- ('Equality', 'Render', 'StringTree', 'Eval')
semanticInstances :: Name -> DecsQ
semanticInstances n =
    [d|
        instance Equality $(typ) where
          equal    = equalDefault
          exprHash = exprHashDefault
        instance Render $(typ) where
          renderSym  = renderSymDefault
          renderArgs = renderArgsDefault
        instance StringTree $(typ)
        instance Eval $(typ) where evaluate = evaluateDefault
    |]
  where
    typ = conT n

