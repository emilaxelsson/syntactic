-- | This module provides binding constructs using higher-order syntax and a
-- function for translating back to first-order syntax. Expressions constructed
-- using the exported interface are guaranteed to have a well-behaved
-- translation.

module Language.Syntactic.Features.Binding.HigherOrder
    ( module Language.Syntactic
    , Variable
    , evalLambda
    , Let (..)
    , HOLambda (..)
    , HOAST
    , lambda
    , lambdaN
    , let_
    , reifyM
    , reify
    ) where



import Control.Monad.State
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Features.Binding



-- | Higher-order lambda binding
data HOLambda dom a
  where
    HOLambda :: (Typeable a, Typeable b)
        => (HOAST dom (Full a) -> HOAST dom (Full b))
        -> HOLambda dom (Full (a -> b))

type HOAST dom = AST (HOLambda dom :+: Variable :+: dom)



-- | Lambda binding
lambda :: (Typeable a, Typeable b) =>
    (HOAST dom (Full a) -> HOAST dom (Full b)) -> HOAST dom (Full (a -> b))
lambda = inject . HOLambda

-- | N-ary lambda binding
lambdaN ::
    ( NAry a
    , NAryDom a ~ (HOLambda dom :+: Variable :+: dom)
    ) =>
      a -> HOAST dom (Full (NAryEval a))
lambdaN = bindN lambda

-- | Let binding
let_ :: (Typeable a, Typeable b, Let :<: dom)
    => HOAST dom (Full a)
    -> (HOAST dom (Full a) -> HOAST dom (Full b))
    -> HOAST dom (Full b)
let_ a f = inject Let :$: a :$: lambda f



reifyM :: Typeable a
    => HOAST dom a
    -> State VarId (AST (Lambda :+: Variable :+: dom) a)
reifyM (f :$: a)            = liftM2 (:$:) (reifyM f) (reifyM a)
reifyM (Symbol (InjectR a)) = return $ Symbol $ InjectR a
reifyM (Symbol (InjectL (HOLambda f))) = do
    v <- get; put (v+1)
    liftM (inject (Lambda v) :$:) $ reifyM $ f $ inject $ Variable v

-- | Translating expressions with higher-order binding to corresponding
-- expressions using first-order binding
reify :: Typeable a => HOAST dom a -> AST (Lambda :+: Variable :+: dom) a
reify = flip evalState 0 . reifyM
  -- It is assumed that there are no 'Variable' constructors (i.e. no free
  -- variables) in the argument. This is guaranteed by the exported interface.

