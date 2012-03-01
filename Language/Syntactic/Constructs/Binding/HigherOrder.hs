{-# LANGUAGE UndecidableInstances #-}

-- | This module provides binding constructs using higher-order syntax and a
-- function for translating to first-order syntax. Expressions constructed using
-- the exported interface are guaranteed to have a well-behaved translation.

module Language.Syntactic.Constructs.Binding.HigherOrder
    ( Variable
    , Let (..)
    , HOLambda (..)
    , HODomain
    , lambda
    , reifyM
    , reifyTop
    , reify
    ) where



import Control.Monad.State
import Data.Typeable

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Constructs.Binding



-- | Higher-order lambda binding
data HOLambda ctx dom a
  where
    HOLambda :: (Typeable a, Typeable b, Sat ctx a)
        => (ASTF (HODomain ctx dom) a -> ASTF (HODomain ctx dom) b)
        -> HOLambda ctx dom (Full (a -> b))

type HODomain ctx dom = HOLambda ctx dom :+: Variable ctx :+: dom

instance WitnessCons (HOLambda ctx dom)
  where
    witnessCons (HOLambda _) = ConsWit

instance MaybeWitnessSat ctx1 (HOLambda ctx2 dom)
  where
    maybeWitnessSat _ _ = Nothing



-- | Lambda binding
lambda :: (Typeable a, Typeable b, Sat ctx a)
    => (ASTF (HODomain ctx dom) a -> ASTF (HODomain ctx dom) b)
    -> ASTF (HODomain ctx dom) (a -> b)
lambda = inject . HOLambda

instance
    ( Syntactic a (HODomain ctx dom)
    , Syntactic b (HODomain ctx dom)
    , Sat ctx (Internal a)
    ) =>
      Syntactic (a -> b) (HODomain ctx dom)
  where
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lambda (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"
      -- TODO An implementation of sugar would require dom to have some kind of
      --      application. Perhaps use Let for this?



reifyM :: forall ctx dom a . Typeable a
    => AST (HODomain ctx dom) a
    -> State VarId (AST (Lambda ctx :+: Variable ctx :+: dom) a)
reifyM (f :$: a)            = liftM2 (:$:) (reifyM f) (reifyM a)
reifyM (Symbol (InjectR a)) = return $ Symbol $ InjectR a
reifyM (Symbol (InjectL (HOLambda f))) = do
    v    <- get; put (v+1)
    body <- reifyM $ f $ inject $ (Variable v `withContext` ctx)
    return $ inject (Lambda v `withContext` ctx) :$: body
  where
    ctx = Proxy :: Proxy ctx

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reifyTop :: Typeable a =>
    AST (HODomain ctx dom) a -> AST (Lambda ctx :+: Variable ctx :+: dom) a
reifyTop = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.

-- | Reifying an n-ary syntactic function
reify :: Syntactic a (HODomain ctx dom)
    => a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) (Internal a)
reify = reifyTop . desugar

