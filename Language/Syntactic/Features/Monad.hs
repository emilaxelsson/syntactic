{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Features.Monad where

import Control.Monad.Cont

import Language.Syntactic
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder

import Data.Typeable
import Data.Hash
import Data.Proxy

-- | Convenient type alias
newtype MonadS ctx dom m a = MonadS { unMonadS :: forall r. (Monad m, Typeable r)
                                               => Cont (HOASTF ctx dom (m r)) a }

deriving instance Functor (MonadS ctx dom m)

instance (Monad m) => Monad (MonadS ctx dom m)
  where
    return a = MonadS $ return a
    ma >>= f = MonadS $ unMonadS ma >>= unMonadS . f

instance ( Monad m, Typeable1 m
         , MonadF m :<: dom
         , Syntactic a (HODomain ctx dom)
         , Sat ctx (Internal a)
         ) =>
         Syntactic (MonadS ctx dom m a) (HODomain ctx dom)
  where
    type Internal (MonadS ctx dom m a) = m (Internal a)
    desugar = desugar . flip runCont (\c -> inject Return :$: desugar c) . unMonadS
    sugar   = liftM sugar . liftMS

instance ( Monad m, Typeable1 m
         , MonadF m :<: dom
         , ia ~ Internal a
         , Syntactic a (HODomain ctx dom)
         , Sat ctx ia
         ) =>
         SyntacticN (MonadS ctx dom m a) (HOASTF ctx dom (m ia))
  where
    desugarN = desugar
    sugarN   = sugar

ret :: (MonadF m :<: dom, Typeable a, Monad m) =>
       ASTF dom a -> ASTF dom (m a)
ret a = inject Return :$: a

bnd :: ( MonadF m :<: dom
        , Monad m, Typeable1 m
        , Sat ctx a, Typeable a, Typeable b
        )
    => HOASTF ctx dom (m a) -> (HOASTF ctx dom a -> HOASTF ctx dom (m b)) -> HOASTF ctx dom (m b)
bnd ma f = inject Bind :$: ma :$: lambda f

thn :: ( MonadF m :<: dom
       , Monad m, Typeable1 m
       , Typeable a, Typeable b
       )
    => HOASTF ctx dom (m a) -> HOASTF ctx dom (m b) -> HOASTF ctx dom (m b)
thn ma mb = inject Then :$: ma :$: mb

liftMS :: ( MonadF m :<: dom
          , Monad m, Typeable1 m
          , Typeable a
          , Sat ctx a
          ) =>
          HOASTF ctx dom (m a) -> MonadS ctx dom m (HOASTF ctx dom a)
liftMS f = MonadS $ cont $ \c -> inject Bind :$: f :$: lambda c

-- | Represents monadic binding in an AST
data MonadF m a
  where
    Return :: MonadF m (a :-> Full (m a))
    Bind   :: MonadF m (m a :-> (a -> m b) :-> Full (m b))
    Then   :: MonadF m (m a :-> m b        :-> Full (m b))

instance Render (MonadF m)
  where
    render Return = "return"
    render Bind   = "bind"
    render Then   = "then"

instance ToTree (MonadF m)

instance (Monad m) => Eval (MonadF m)
  where
    evaluate Return = fromEval return
    evaluate Bind   = fromEval (>>=)
    evaluate Then   = fromEval (>>)

instance ExprEq (MonadF m)
  where
    exprEq Return Return = True
    exprEq Bind   Bind   = True
    exprEq Then   Then   = True
    exprEq _      _      = False

    exprHash Return = hashInt 0
    exprHash Bind   = hashInt 1
    exprHash Then   = hashInt 2

instance WitnessCons (MonadF m) where witnessCons Bind = ConsWit

instance MaybeWitnessSat ctx (MonadF m)
  where
    maybeWitnessSat _ _ = Nothing

instance (Monad m) => EvalBind (MonadF m) where evalBindFeat = evalBindFeatDefault

prjMonad :: (MonadF m :<: sup) => Proxy (m ()) -> sup a -> Maybe (MonadF m a)
prjMonad _ = project
