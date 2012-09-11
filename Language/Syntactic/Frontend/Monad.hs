{-# LANGUAGE UndecidableInstances #-}

-- | Monadic constructs
--
-- This module is based on the paper
-- /Generic Monadic Constructs for Embedded Languages/ (Persson et al., IFL 2011
-- <http://www.cse.chalmers.se/~emax/documents/persson2011generic.pdf>).

module Language.Syntactic.Frontend.Monad where



import Control.Monad.Cont
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Monad



-- TODO Unfortunately, this module hard-codes the use of `Typeable`. The problem
--      is this: Say we replace `Typeable` in the definition of `Mon` by a
--      parameter `p`. Then `sugarMonad` will get a constraint `p (a -> m r)`.
--      But `r` existentially quantified and can only be constrained in the
--      definition of `Mon`. With `Typeable` this works because
--      `(Typeable1 m, Typeable a, Typeable r)` implies `Typeable (a -> m r)`.

-- | User interface to embedded monadic programs
newtype Mon dom m a
  where
    Mon
        :: { unMon :: forall r
                   .  (Monad m, Typeable r, InjectC (MONAD m) dom (m r))
                   => Cont (ASTF (HODomain dom Typeable) (m r)) a
           }
        -> Mon dom m a

deriving instance Functor (Mon dom m)

instance (Monad m) => Monad (Mon dom m)
  where
    return a = Mon $ return a
    ma >>= f = Mon $ unMon ma >>= unMon . f

-- | One-layer desugaring of monadic actions
desugarMonad
    :: ( InjectC (MONAD m) dom (m a)
       , Monad m
       , Typeable1 m
       , Typeable a
       )
    => Mon dom m (ASTF (HODomain dom Typeable) a)
    -> ASTF (HODomain dom Typeable) (m a)
desugarMonad = flip runCont (sugarSymC Return) . unMon

-- | One-layer sugaring of monadic actions
sugarMonad
    :: ( Monad m
       , Typeable1 m
       , Typeable a
       )
    => ASTF (HODomain dom Typeable) (m a)
    -> Mon dom m (ASTF (HODomain dom Typeable) a)
sugarMonad ma = Mon $ cont $ sugarSymC Bind ma

instance ( Syntactic a (HODomain dom Typeable)
         , InjectC (MONAD m) dom (m (Internal a))
         , Monad m
         , Typeable1 m
         , Typeable (Internal a)
         ) =>
           Syntactic (Mon dom m a) (HODomain dom Typeable)
  where
    type Internal (Mon dom m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

