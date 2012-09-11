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
    , lambda
    , reifyM
    , reifyTop
    , reify
    ) where



import Control.Monad.State

import Language.Syntactic
import Language.Syntactic.Constructs.Binding



-- | Higher-order lambda binding
data HOLambda dom p a
  where
    HOLambda
        :: p a
        => (ASTF (HODomain dom p) a -> ASTF (HODomain dom p) b)
        -> HOLambda dom p (Full (a -> b))

type HODomain dom p = (HOLambda dom p :+: Variable :+: dom) :|| p

instance Constrained (HOLambda dom p)
  where
    type Sat (HOLambda dom p) = Top
    exprDict _ = Dict



-- | Lambda binding
lambda
    :: (p a, p (a -> b))
    => (ASTF (HODomain dom p) a -> ASTF (HODomain dom p) b)
    -> ASTF (HODomain dom p) (a -> b)
lambda = injC . HOLambda

instance
    ( Syntactic a (HODomain dom p)
    , Syntactic b (HODomain dom p)
    , p (Internal a)
    , p (Internal a -> Internal b)
    ) =>
      Syntactic (a -> b) (HODomain dom p)
  where
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lambda (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"
      -- TODO An implementation of sugar would require dom to have some kind of
      --      application. Perhaps use `Let` for this?



reifyM
    :: AST (HODomain dom p) a
    -> State VarId (AST ((Lambda :+: Variable :+: dom) :|| p) a)
reifyM (f :$ a)            = liftM2 (:$) (reifyM f) (reifyM a)
reifyM (Sym (C' (InjR a))) = return $ Sym $ C' $ InjR a
reifyM (Sym (C' (InjL (HOLambda f)))) = do
    v    <- get; put (v+1)
    body <- reifyM $ f $ injC (Variable v)
    return $ injC (Lambda v) :$ body

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reifyTop ::
    AST (HODomain dom p) a -> AST ((Lambda :+: Variable :+: dom) :|| p) a
reifyTop = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.

-- | Reify an n-ary syntactic function
reify :: Syntactic a (HODomain dom p) =>
    a -> ASTF ((Lambda :+: Variable :+: dom) :|| p) (Internal a)
reify = reifyTop . desugar

