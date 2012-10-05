{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module NanoFeldspar.Extra where



import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Binding.Optimize
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Sharing.Graph
import Language.Syntactic.Sharing.ReifyHO

import NanoFeldspar.Core



--------------------------------------------------------------------------------
-- * Graph reification
--------------------------------------------------------------------------------

-- | A predicate deciding which constructs can be shared. Literals and variables
-- are not shared.
canShare :: ASTF FeldDomainAll a -> Bool
canShare (prj             -> Just (Literal _))       = False
canShare (prjC' (Variable 0) pTop -> Just (C' (Variable _))) = False
canShare a = True

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

instance Optimize ForLoop
  where
    optimizeSym = optimizeSymDefault

instance Optimize Parallel
  where
    optimizeSym = optimizeSymDefault

constFold :: forall a
    .  ASTF ((FODomain (Let :+: (FeldDomain :|| Eq :| Show))) Typeable Top) a
    -> a
    -> ASTF ((FODomain (Let :+: (FeldDomain :|| Eq :| Show))) Typeable Top) a
constFold expr a = match (\sym _ -> case sym of
      C' (InjR (InjR (InjR (C (C' _))))) -> injC (Literal a)
      _ -> expr
    ) expr

drawFeldPart :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldPart = drawAST . optimize constFold . reify

