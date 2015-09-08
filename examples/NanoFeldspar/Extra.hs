{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}

module NanoFeldspar.Extra where



import Control.Monad.State
import Data.Typeable

import Language.Syntactic as Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Binding.Optimize
import Language.Syntactic.Constructs.Construct
import Language.Syntactic.Constructs.Literal
import Language.Syntactic.Sharing.SimpleCodeMotion
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
drawCSE :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> IO ()
drawCSE a = do
    (g,_) <- reifyGraph canShare2 a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ cse
      $ g

-- | Draw the syntax graph after observing sharing
drawObs :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> IO ()
drawObs a = do
    (g,_) <- reifyGraph canShare2 a
    drawASG
      $ reindexNodesFrom0
      $ inlineSingle
      $ g



--------------------------------------------------------------------------------
-- * Simplification/constant folding
--------------------------------------------------------------------------------

instance Optimize ForLoop
  where
    {-# SPECIALIZE instance Optimize ForLoop #-}
    {-# INLINABLE optimizeSym #-}
    optimizeSym = optimizeSymDefault

instance Optimize Parallel
  where
    {-# SPECIALIZE instance Optimize Parallel #-}
    {-# INLINABLE optimizeSym #-}
    optimizeSym = optimizeSymDefault

constFold :: forall a
    .  ASTF ((FODomain (Let :+: (FeldDomain :|| Eq :| Show))) Typeable Top) a
    -> a
    -> ASTF ((FODomain (Let :+: (FeldDomain :|| Eq :| Show))) Typeable Top) a
constFold expr a = match (\sym _ -> case sym of
      C' (InjR (InjR (InjR (C (C' _))))) -> injC (Literal a)
      _ -> expr
    ) expr

reifySimp :: (Syntactic a, Domain a ~ FeldDomainAll) =>
    a -> ASTF ((FODomain (Let :+: (FeldDomain :|| Eq :| Show))) Typeable Top) (Internal a)
reifySimp = flip evalState 0 .
    (   codeMotion (const True) prjDictFO canShareDict
    .   optimize constFold
    <=< reifyM
    .   desugar
    )

drawSimp :: (Syntactic a, Domain a ~ FeldDomainAll) => a -> IO ()
drawSimp = Syntactic.drawAST . reifySimp
