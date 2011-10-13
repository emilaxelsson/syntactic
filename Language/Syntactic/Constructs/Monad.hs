{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Constructs.Monad where

import qualified Control.Monad.Cont as CMC
import Control.Monad.Cont hiding (when)

import Language.Syntactic
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder

import Data.Typeable
import Data.Hash
import Data.Proxy

-- | Convenient type alias
newtype MonadS ctx dom m a = MonadS
    { unMonadS :: forall r. (Monad m, Typeable r)
               => Cont (ASTF (HODomain ctx dom) (m r)) a
    }

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
    desugar = desugar . flip runCont (appSym Return . desugar) . unMonadS
    sugar   = liftM sugar . liftMS

liftMS :: ( MonadF m :<: dom
          , Monad m, Typeable1 m
          , Typeable a
          , Sat ctx a
          ) =>
          ASTF (HODomain ctx dom) (m a) -> MonadS ctx dom m (ASTF (HODomain ctx dom) a)
liftMS ma = MonadS $ cont $ \c -> sugarSym Bind ma c

-- | Represents monadic binding in an AST
data MonadF m a
  where
    Return :: MonadF m (a    :-> Full (m a))
    Bind   :: MonadF m (m a  :-> (a -> m b) :-> Full (m b))
    Then   :: MonadF m (m a  :-> m b        :-> Full (m b))

    When   :: MonadF m (Bool :-> m ()       :-> Full (m ()))

instance Render (MonadF m)
  where
    render Return = "return"
    render Bind   = "bind"
    render Then   = "then"
    render When   = "when"

instance ToTree (MonadF m)

instance (Monad m) => Eval (MonadF m)
  where
    evaluate Return = fromEval return
    evaluate Bind   = fromEval (>>=)
    evaluate Then   = fromEval (>>)
    evaluate When   = fromEval CMC.when

instance ExprEq (MonadF m)
  where
    exprEq Return Return = True
    exprEq Bind   Bind   = True
    exprEq Then   Then   = True
    exprEq When   When   = True
    exprEq _      _      = False

    exprHash Return = hashInt 0
    exprHash Bind   = hashInt 1
    exprHash Then   = hashInt 2
    exprHash When   = hashInt 3

instance WitnessCons (MonadF m) where witnessCons Bind = ConsWit

instance MaybeWitnessSat ctx (MonadF m)
  where
    maybeWitnessSat _ _ = Nothing

instance (Monad m) => EvalBind (MonadF m) where evalBindSym = evalBindSymDefault

prjMonad :: (MonadF m :<: sup) => Proxy (m ()) -> sup a -> Maybe (MonadF m a)
prjMonad _ = project
