{-# LANGUAGE TemplateHaskell #-}

-- | Default implementations of some interpretation functions

module Data.Syntactic.Interpretation.Default where



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
-- `equal` via the `Default` class.
data Def a
  where
    Def
        :: { defaultName :: String
           , defaultEval :: Denotation a
           }
        -> Def a

instance Equality Def
  where
    equal (Def a _) (Def b _) = a==b
    exprHash (Def name _)     = hash name

instance Render Def
  where
    renderSym (Def name _) = name

    renderArgs [] (Def name _) = name
    renderArgs args (Def name _)
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

instance Eval Def
  where
    evaluate (Def _ a) = a



-- | Class of expressions that can be treated as constructs
class Default expr
  where
    defaultSym :: expr a -> Def a

-- | Default implementation of 'equal'
equalDefault :: Default expr => expr a -> expr b -> Bool
equalDefault a b = equal (defaultSym a) (defaultSym b)

-- | Default implementation of 'exprHash'
exprHashDefault :: Default expr => expr a -> Hash
exprHashDefault = exprHash . defaultSym

-- | Default implementation of 'renderSym'
renderSymDefault :: Default expr => expr a -> String
renderSymDefault = renderSym . defaultSym

-- | Default implementation of 'renderArgs'
renderArgsDefault :: Default expr => [String] -> expr a -> String
renderArgsDefault args = renderArgs args . defaultSym

-- | Default implementation of 'evaluate'
evaluateDefault :: Default expr => expr a -> Denotation a
evaluateDefault = evaluate . defaultSym

-- | Derive instances for interpretation classes ('Equality', 'Render', 'StringTree', 'Eval')
interpretationInstances :: Name -> DecsQ
interpretationInstances n =
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

