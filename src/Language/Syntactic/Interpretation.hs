{-# LANGUAGE TemplateHaskell #-}

module Language.Syntactic.Interpretation where

import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Language.Syntactic.Interpretation.Equality
import Language.Syntactic.Interpretation.Render
import Language.Syntactic.Interpretation.Evaluation

-- | Derive instances for 'Semantic' related classes
-- ('Equality', 'Render', 'StringTree', 'Eval')
semanticInstances :: Name -> DecsQ
semanticInstances n =
    [d|
        instance Equality $(typ)
        instance Render $(typ)
        instance StringTree $(typ)
        instance Eval $(typ) where
          {-# SPECIALIZE instance Eval $(typ) #-}
    |]
  where
    typ = conT n
