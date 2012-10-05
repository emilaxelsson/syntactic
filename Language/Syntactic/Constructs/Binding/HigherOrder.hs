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
    , FunCompositional (..)
    , lambda
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

type HODomain dom p pVar = (HOLambda dom p pVar :+: (Variable :|| pVar) :+: dom) :|| p

type FODomain dom p pVar = (SubConstr2 Lambda pVar Top :+: (Variable :|| pVar) :+: dom) :|| p

instance EvalBind dom => EvalBind (SubConstr2 dom pa pb)
  where
    evalBindSym (SubConstr2 a) = evalBindSym a

instance AlphaEq sub sub dom env => AlphaEq (SubConstr2 sub pa pb) (SubConstr2 sub pa pb) dom env
  where
    alphaEqSym (SubConstr2 a) aArgs (SubConstr2 b) bArgs = alphaEqSym a aArgs b bArgs

class FunCompositional p
  where
    funCompose :: Dict (p a) -> Dict (p b) -> Dict (p (a -> b))



-- | Lambda binding
lambda
    :: (p (a -> b), p a, pVar a)
    => (ASTF (HODomain dom p pVar) a -> ASTF (HODomain dom p pVar) b)
    -> ASTF (HODomain dom p pVar) (a -> b)
lambda = injC . HOLambda

instance
    ( Syntactic a (HODomain dom p pVar)
    , Syntactic b (HODomain dom p pVar)
    , p (Internal a -> Internal b)
    , p (Internal a)
    , pVar (Internal a)
    ) =>
      Syntactic (a -> b) (HODomain dom p pVar)
  where
    type Internal (a -> b) = Internal a -> Internal b
    desugar f = lambda (desugar . f . sugar)
    sugar     = error "sugar not implemented for (a -> b)"
      -- TODO An implementation of sugar would require dom to have some kind of
      --      application. Perhaps use `Let` for this?



reifyM :: forall dom p pVar a
    .  AST (HODomain dom p pVar) a
    -> State VarId (AST (FODomain dom p pVar) a)
reifyM (f :$ a)            = liftM2 (:$) (reifyM f) (reifyM a)
reifyM (Sym (C' (InjR a))) = return $ Sym $ C' $ InjR a
reifyM (Sym (C' (InjL lam@(HOLambda f)))) = do
    v    <- get; put (v+1)
    body <- reifyM $ f $ injC $ constr' pProxy (Variable v)
    return $ injC (subConstr2 pProxy pTop (Lambda v)) :$ body
  where
    pProxy = PProxy :: PProxy pVar

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reifyTop :: AST (HODomain dom p pVar) a -> AST (FODomain dom p pVar) a
reifyTop = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.

-- | Reify an n-ary syntactic function
reify :: Syntactic a (HODomain dom p pVar) =>
    a -> ASTF (FODomain dom p pVar) (Internal a)
reify = reifyTop . desugar

