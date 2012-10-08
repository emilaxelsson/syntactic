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

-- | A predicate deciding which constructs can be shared. Variables, lambdas and literals are not
-- shared.
canShare2 :: ASTF (HODomain FeldSyms Typeable Top) a -> Bool
canShare2 (prjP (P::P (Variable :|| Top))               -> Just _) = False
canShare2 (prjP (P::P (HOLambda FeldSyms Typeable Top)) -> Just _) = False
canShare2 (prj -> Just (Literal _)) = False
canShare2 _  = True

-- | Draw the syntax graph after common sub-expression elimination
drawFeldCSE :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldCSE a = do
    (g,_) <- reifyGraph canShare2 a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ cse
      $ g

-- | Draw the syntax graph after observing sharing
drawFeldObs :: Syntactic a FeldDomainAll => a -> IO ()
drawFeldObs a = do
    (g,_) <- reifyGraph canShare2 a
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

