{-# LANGUAGE UndecidableInstances #-}

-- | This module provides binding constructs using higher-order syntax and a
-- function for translating to first-order syntax. Expressions constructed using
-- the exported interface are guaranteed to have a well-behaved translation.

module Language.Syntactic.Features.Binding.HigherOrder
    ( Variable
    , evalLambda
    , Let (..)
    , HOLambda (..)
    , HOAST
    , HOASTF
    , lambdaCtx
    , lambda
    , lambdaNCtx
    , lambdaN
    , letBindCtx
    , letBind
    , reifyM
    , reifyHOAST
    , Reifiable
    , reifyCtx
    , reify
    ) where



import Control.Monad.State
import Data.Typeable

import Data.Proxy

import Language.Syntactic
import Language.Syntactic.Features.Binding



-- | Higher-order lambda binding
data HOLambda ctx dom a
  where
    HOLambda :: (Typeable a, Typeable b, Sat ctx a)
        => Proxy ctx
        -> (HOAST ctx dom (Full a) -> HOAST ctx dom (Full b))
        -> HOLambda ctx dom (Full (a -> b))

type HOAST  ctx dom a = AST (HOLambda ctx dom :+: Variable ctx :+: dom) a
type HOASTF ctx dom a = HOAST ctx dom (Full a)

instance WitnessCons (HOLambda ctx dom)
  where
    witnessCons (HOLambda _ _) = ConsWit



-- | Lambda binding with explicit context
lambdaCtx :: (Typeable a, Typeable b, Sat ctx a)
    => Proxy ctx
    -> (HOAST ctx dom (Full a) -> HOAST ctx dom (Full b))
    -> HOAST ctx dom (Full (a -> b))
lambdaCtx ctx = inject . HOLambda ctx

-- | Lambda binding
lambda :: (Typeable a, Typeable b)
    => (HOAST Poly dom (Full a) -> HOAST Poly dom (Full b))
    -> HOAST Poly dom (Full (a -> b))
lambda = lambdaCtx poly

-- | N-ary lambda binding with explicit context
lambdaNCtx :: NAry ctx a (HOLambda ctx dom :+: Variable ctx :+: dom) =>
    Proxy ctx -> a -> HOAST ctx dom (Full (NAryEval a))
lambdaNCtx ctx = bindN ctx (lambdaCtx ctx)

-- | N-ary lambda binding
lambdaN :: NAry Poly a (HOLambda Poly dom :+: Variable Poly :+: dom) =>
    a -> HOAST Poly dom (Full (NAryEval a))
lambdaN = lambdaNCtx poly

-- | Let binding with explicit context
letBindCtx
    :: (Typeable a, Typeable b, Let ctxa ctxb :<: dom, Sat ctxa a, Sat ctxb b)
    => Proxy ctxa
    -> Proxy ctxb
    -> HOAST ctxa dom (Full a)
    -> (HOAST ctxa dom (Full a) -> HOAST ctxa dom (Full b))
    -> HOAST ctxa dom (Full b)
letBindCtx ctxa ctxb a f = inject (Let ctxa ctxb) :$: a :$: lambdaCtx ctxa f

-- | Let binding
letBind :: (Typeable a, Typeable b, Let Poly Poly :<: dom)
    => HOAST Poly dom (Full a)
    -> (HOAST Poly dom (Full a) -> HOAST Poly dom (Full b))
    -> HOAST Poly dom (Full b)
letBind = letBindCtx poly poly



reifyM :: Typeable a
    => HOAST ctx dom a
    -> State VarId (AST (Lambda ctx :+: Variable ctx :+: dom) a)
reifyM (f :$: a)            = liftM2 (:$:) (reifyM f) (reifyM a)
reifyM (Symbol (InjectR a)) = return $ Symbol $ InjectR a
reifyM (Symbol (InjectL (HOLambda ctx f))) = do
    v <- get; put (v+1)
    liftM (inject (Lambda ctx v) :$:) $ reifyM $ f $ inject $ Variable ctx v

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reifyHOAST :: Typeable a =>
    HOAST ctx dom a -> AST (Lambda ctx :+: Variable ctx :+: dom) a
reifyHOAST = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.



-- | Convenient class alias for n-ary syntactic functions
class
    ( SyntacticN a internal
    , NAry ctx internal (HOLambda ctx dom :+: Variable ctx :+: dom)
    , Typeable (NAryEval internal)
    ) =>
      Reifiable ctx a dom internal | a -> dom internal

instance
    ( SyntacticN a internal
    , NAry ctx internal (HOLambda ctx dom :+: Variable ctx :+: dom)
    , Typeable (NAryEval internal)
    ) =>
      Reifiable ctx a dom internal

-- | Reifying an n-ary syntactic function with explicit context
reifyCtx :: Reifiable ctx a dom internal
    => Proxy ctx
    -> a
    -> ASTF (Lambda ctx :+: Variable ctx :+: dom) (NAryEval internal)
reifyCtx ctx = reifyHOAST . lambdaNCtx ctx . desugarN

-- | Reifying an n-ary syntactic function
reify :: Reifiable Poly a dom internal =>
    a -> ASTF (Lambda Poly :+: Variable Poly :+: dom) (NAryEval internal)
reify = reifyCtx poly

