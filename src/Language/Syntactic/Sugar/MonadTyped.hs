{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#if __GLASGOW_HASKELL__ < 708
#define TYPEABLE Typeable1
#else
#define TYPEABLE Typeable
#endif

-- | 'Syntactic' instance for 'Remon' for domains based on 'Typed' and
-- 'BindingT'

module Language.Syntactic.Sugar.MonadTyped where



import Control.Monad.Cont
import Data.Typeable

import Language.Syntactic
import Language.Syntactic.Functional
import Language.Syntactic.Sugar.BindingTyped ()



-- | One-layer sugaring of monadic actions
sugarMonad
    :: ( sym ~ Typed s
       , BindingT :<: s
       , MONAD m  :<: s
       , TYPEABLE m
       , Typeable a
       )
    => ASTF sym (m a) -> Remon sym m (ASTF sym a)
sugarMonad ma = Remon $ cont $ sugarSymTyped Bind ma

instance
    ( sym ~ Typed s
    , Syntactic a, Domain a ~ sym
    , BindingT :<: s
    , MONAD m  :<: s
    , TYPEABLE m
    , Typeable (Internal a)
    ) =>
      Syntactic (Remon sym m a)
  where
    type Domain (Remon sym m a)   = sym
    type Internal (Remon sym m a) = m (Internal a)
    desugar = desugarMonadTyped . fmap desugar
    sugar   = fmap sugar   . sugarMonad

