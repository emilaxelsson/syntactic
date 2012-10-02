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
newtype Mon dom pVar m a
  where
    Mon
        :: { unMon :: forall r
                   .  (Monad m, Typeable r, InjectC (MONAD m) dom (m r))
                   => Cont (ASTF (HODomain dom Typeable pVar) (m r)) a
           }
        -> Mon dom pVar m a

deriving instance Functor (Mon dom pVar m)

instance (Monad m) => Monad (Mon dom pVar m)
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
    => Mon dom pVar m (ASTF (HODomain dom Typeable pVar) a)
    -> ASTF (HODomain dom Typeable pVar) (m a)
desugarMonad = flip runCont (sugarSymC Return) . unMon

-- | One-layer sugaring of monadic actions
sugarMonad
    :: ( Monad m
       , Typeable1 m
       , Typeable a
       , pVar a
       )
    => ASTF (HODomain dom Typeable pVar) (m a)
    -> Mon dom pVar m (ASTF (HODomain dom Typeable pVar) a)
sugarMonad ma = Mon $ cont $ sugarSymC Bind ma

instance ( Syntactic a (HODomain dom Typeable pVar)
         , InjectC (MONAD m) dom (m (Internal a))
         , Monad m
         , Typeable1 m
         , Typeable (Internal a)
         , pVar (Internal a)
         ) =>
           Syntactic (Mon dom pVar m a) (HODomain dom Typeable pVar)
  where
    type Internal (Mon dom pVar m a) = m (Internal a)
    desugar = desugarMonad . fmap desugar
    sugar   = fmap sugar   . sugarMonad

