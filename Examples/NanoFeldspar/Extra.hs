{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

module NanoFeldspar.Extra where



import Language.Syntactic
import Language.Syntactic.Features.Symbol
import Language.Syntactic.Features.Literal
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Features.Binding.PartialEval
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.ReifyHO

import NanoFeldspar.Core



-- | A predicate deciding which constructs can be shared. Variables and literals
-- are not shared.
mkSimpleWit :: (Sym SimpleCtx :<: dom, Parallel :<: dom, ForLoop :<: dom) =>
    ASTF dom a -> Maybe (Witness' SimpleCtx a)
mkSimpleWit ((project -> Just Parallel) :$: _ :$: _)      = Just Witness'
mkSimpleWit ((project -> Just ForLoop) :$: _ :$: _ :$: _) = Just Witness'
mkSimpleWit expr = witnessSatSym simpleCtx expr



--------------------------------------------------------------------------------
-- * Graph reification
--------------------------------------------------------------------------------

-- | Draw the syntax graph after common sub-expression elimination
drawFeldCSE :: Reifiable SimpleCtx a FeldDomain internal => a -> IO ()
drawFeldCSE a = do
    (g,_) <- reifyGraph mkSimpleWit a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ cse
      $ g

-- | Draw the syntax graph after observing sharing
drawFeldObs :: Reifiable SimpleCtx a FeldDomain internal => a -> IO ()
drawFeldObs a = do
    (g,_) <- reifyGraph mkSimpleWit a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ g

--------------------------------------------------------------------------------
-- * Partial evaluation
--------------------------------------------------------------------------------

instance (ForLoop :<: dom, PartialEval dom ctx dom) =>
    PartialEval ForLoop ctx dom
  where
    partEvalFeat = partEvalFeatDefault

instance (Parallel :<: dom, PartialEval dom ctx dom) =>
    PartialEval Parallel ctx dom
  where
    partEvalFeat = partEvalFeatDefault



constFold :: forall a
    .  ASTF (Lambda SimpleCtx :+: Variable SimpleCtx :+: FeldDomain) a
    -> a
    -> ASTF (Lambda SimpleCtx :+: Variable SimpleCtx :+: FeldDomain) a
constFold expr a = case mkSimpleWit expr of
    Just Witness' -> case witness :: Witness SimpleCtx a of
        SimpleWit -> litCtx simpleCtx a
    _ -> expr

drawFeldPart :: Reifiable SimpleCtx a FeldDomain internal => a -> IO ()
drawFeldPart = drawAST . partialEval simpleCtx constFold . reifyCtx simpleCtx

