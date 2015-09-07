{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

-- | This module provides binding constructs using higher-order syntax and a
-- function ('reify') for translating to first-order syntax. Expressions
-- constructed using the exported interface (specifically, not introducing
-- 'Variable's explicitly) are guaranteed to have well-behaved translation.

module Language.Syntactic.Constructs.Binding.HigherOrder
    ( Variable
    , Let (..)
    , HOLambda (..)
    , HODomain
    , FODomain
    , CLambda
    , IsHODomain (..)
    , reifyM
    , reifyTop
    , reify
    ) where



import Control.Monad.State

import Language.Syntactic
import Language.Syntactic.Constructs.Binding



-- | Higher-order lambda binding
data HOLambda dom p pVar a
  where
    HOLambda
        :: (p a, pVar a)
        => (ASTF (HODomain dom p pVar) a -> ASTF (HODomain dom p pVar) b)
        -> HOLambda dom p pVar (Full (a -> b))

-- | Adding support for higher-order abstract syntax to a domain
type HODomain dom p pVar = (HOLambda dom p pVar :+: (Variable :|| pVar) :+: dom) :|| p

-- | Equivalent to 'HODomain' (including type constraints), but using a first-order representation
-- of binding
type FODomain dom p pVar = (CLambda pVar :+: (Variable :|| pVar) :+: dom) :|| p

-- | 'Lambda' with a constraint on the bound variable type
type CLambda pVar = SubConstr2 (->) Lambda pVar Top



-- | An abstraction of 'HODomain'
class IsHODomain dom p pVar | dom -> p pVar
  where
    lambda :: (p (a -> b), p a, pVar a) => (ASTF dom a -> ASTF dom b) -> ASTF dom (a -> b)

instance IsHODomain (HODomain dom p pVar) p pVar
  where
    {-# SPECIALIZE instance IsHODomain (HODomain dom p pVar) p pVar #-}
    {-# INLINABLE lambda #-}
    lambda = injC . HOLambda

instance
    ( Syntactic a, Domain a ~ dom
    , Syntactic b, Domain b ~ dom
    , IsHODomain dom p pVar
    , p (Internal a -> Internal b)
    , p (Internal a)
    , pVar (Internal a)
    ) =>
      Syntactic (a -> b)
  where
    {-# SPECIALIZE instance ( Syntactic a, Domain a ~ dom
                            , Syntactic b, Domain b ~ dom
                            , IsHODomain dom p pVar
                            , p (Internal a -> Internal b)
                            , p (Internal a)
                            , pVar (Internal a)
                            ) => Syntactic (a -> b) #-}
    {-# INLINABLE desugar #-}
    {-# INLINABLE sugar #-}
    type Domain (a -> b)   = Domain a
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lambda (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"
      -- TODO An implementation of sugar would require dom to have some kind of
      --      application. Perhaps use `Let` for this?



reifyM :: forall dom p pVar m a
       .  MonadState VarId m
       => AST (HODomain dom p pVar) a -> m (AST (FODomain dom p pVar) a)
reifyM (f :$ a)            = liftM2 (:$) (reifyM f) (reifyM a)
reifyM (Sym (C' (InjR a))) = return $ Sym $ C' $ InjR a
reifyM (Sym (C' (InjL (HOLambda f)))) = do
    v    <- get; put (v+1)
    body <- reifyM $ f $ injC $ symType pVar $ C' (Variable v)
    return $ injC (symType pLam $ SubConstr2 (Lambda v)) :$ body
  where
    pVar = P::P (Variable :|| pVar)
    pLam = P::P (CLambda pVar)

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reifyTop :: AST (HODomain dom p pVar) a -> AST (FODomain dom p pVar) a
reifyTop = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.

-- | Reify an n-ary syntactic function
reify :: (Syntactic a, Domain a ~ HODomain dom p pVar) =>
    a -> ASTF (FODomain dom p pVar) (Internal a)
reify = reifyTop . desugar
