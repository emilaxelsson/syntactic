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
    , lambda
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
        => (HOASTF ctx dom a -> HOASTF ctx dom b)
        -> HOLambda ctx dom (Full (a -> b))

type HOAST  ctx dom a = AST (HOLambda ctx dom :+: Variable ctx :+: dom) a
type HOASTF ctx dom a = HOAST ctx dom (Full a)

instance WitnessCons (HOLambda ctx dom)
  where
    witnessCons (HOLambda _) = ConsWit



-- | Lambda binding
lambda :: (Typeable a, Typeable b, Sat ctx a) =>
    (HOASTF ctx dom a -> HOASTF ctx dom b) -> HOASTF ctx dom (a -> b)
lambda = inject . HOLambda

-- | N-ary lambda binding
lambdaN :: forall ctx dom a
    .  NAry ctx a (HOLambda ctx dom :+: Variable ctx :+: dom)
    => a -> HOASTF ctx dom (NAryEval a)
lambdaN = bindN (Proxy :: Proxy ctx) lambda

-- | Let binding with explicit context
letBindCtx :: forall ctxa ctxb dom a b
    .  (Typeable a, Typeable b, Let ctxa ctxb :<: dom, Sat ctxa a, Sat ctxb b)
    => Proxy ctxb
    -> HOASTF ctxa dom a
    -> (HOASTF ctxa dom a -> HOASTF ctxa dom b)
    -> HOASTF ctxa dom b
letBindCtx _ a f = inject let' :$: a :$: lambda f
  where
    let' :: Let ctxa ctxb (a :-> (a -> b) :-> Full b)
    let' = Let

-- | Let binding
letBind :: (Typeable a, Typeable b, Let Poly Poly :<: dom)
    => HOASTF Poly dom a
    -> (HOASTF Poly dom a -> HOASTF Poly dom b)
    -> HOASTF Poly dom b
letBind = letBindCtx poly



reifyM :: forall ctx dom a . Typeable a
    => HOAST ctx dom a
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
reifyCtx _ = reifyHOAST . lambdaN . desugarN

-- | Reifying an n-ary syntactic function
reify :: Reifiable Poly a dom internal =>
    a -> ASTF (Lambda Poly :+: Variable Poly :+: dom) (NAryEval internal)
reify = reifyCtx poly

