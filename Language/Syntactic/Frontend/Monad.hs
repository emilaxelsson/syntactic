module Language.Syntactic.Frontend.Monad where



import Control.Monad.Cont
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Monad



-- | User interface to embedded monadic programs
newtype Mon ctx dom m a
  where
    Mon
        :: { unMon :: forall r . (Monad m, Typeable r) =>
               Cont (ASTF (HODomain ctx dom) (m r)) a
           }
        -> Mon ctx dom m a

deriving instance Functor (Mon ctx dom m)

instance (Monad m) => Monad (Mon ctx dom m)
  where
    return a = Mon $ return a
    ma >>= f = Mon $ unMon ma >>= unMon . f

-- | One-layer desugaring of monadic actions
desugarMonad
    :: ( MONAD m :<: dom
       , Monad m
       , Typeable1 m
       , Typeable a
       , Sat ctx a
       )
    => Mon ctx dom m (ASTF (HODomain ctx dom) a)
    -> ASTF (HODomain ctx dom) (m a)
desugarMonad = flip runCont (sugarSym Return) . unMon

-- | One-layer sugaring of monadic actions
sugarMonad
    :: ( MONAD m :<: dom
       , Monad m
       , Typeable1 m
       , Typeable a
       , Sat ctx a
       )
    => ASTF (HODomain ctx dom) (m a)
    -> Mon ctx dom m (ASTF (HODomain ctx dom) a)
sugarMonad ma = Mon $ cont $ sugarSym Bind ma

instance ( MONAD m :<: dom
         , Syntactic a (HODomain ctx dom)
         , Monad m, Typeable1 m
         , Sat ctx (Internal a)
         ) =>
         Syntactic (Mon ctx dom m a) (HODomain ctx dom)
  where
    type Internal (Mon ctx dom m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

