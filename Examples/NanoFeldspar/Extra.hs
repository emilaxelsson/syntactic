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
import Language.Syntactic.Features.Binding.Optimize
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.ReifyHO

import NanoFeldspar.Core



--------------------------------------------------------------------------------
-- * Graph reification
--------------------------------------------------------------------------------

-- | A predicate deciding which constructs can be shared. Literals and variables
-- are not shared.
canShare :: ASTF FeldDomainAll a -> Maybe (SatWit SimpleCtx a)
canShare (prjCtx simpleCtx -> Just (Literal _))  = Nothing
canShare (prjCtx simpleCtx -> Just (Variable _)) = Nothing
canShare a = maybeWitnessSat simpleCtx a

-- | Draw the syntax graph after common sub-expression elimination
drawFeldCSE :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldCSE a = do
    (g,_) <- reifyGraph canShare a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ cse
      $ g

-- | Draw the syntax graph after observing sharing
drawFeldObs :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldObs a = do
    (g,_) <- reifyGraph canShare a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ g



--------------------------------------------------------------------------------
-- * Partial evaluation
--------------------------------------------------------------------------------

instance (ForLoop :<: dom, Optimize dom ctx dom) =>
    Optimize ForLoop ctx dom
  where
    optimizeFeat = optimizeFeatDefault

instance (Parallel :<: dom, Optimize dom ctx dom) =>
    Optimize Parallel ctx dom
  where
    optimizeFeat = optimizeFeatDefault

constFold :: forall a
    .  ASTF (Lambda SimpleCtx :+: Variable SimpleCtx :+: FeldDomain) a
    -> a
    -> ASTF (Lambda SimpleCtx :+: Variable SimpleCtx :+: FeldDomain) a
constFold expr a = case fmap fromSatWit (maybeWitnessSat simpleCtx expr) of
    Just SimpleWit -> appSymCtx simpleCtx $ Literal a
    _ -> expr

drawFeldPart :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldPart = drawAST . optimize simpleCtx constFold . reify simpleCtx

