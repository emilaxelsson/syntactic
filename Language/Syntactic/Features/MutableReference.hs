{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Features.MutableReference
  ( MutableReference(..)
  , Ref
  , newRef
  , getRef
  , setRef
  , modifyRef
  )
where

import Language.Syntactic
import Language.Syntactic.Features.Monad
import Language.Syntactic.Features.Mutable
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Features.Binding.Optimize
import qualified Data.IORef as Ref

import Unsafe.Coerce
import Data.Typeable
import Data.Hash

data MutableReference a
  where
    NewRef :: MutableReference (a :-> Full (IO (Ref.IORef a)))
    GetRef :: MutableReference (Ref.IORef a :-> Full (IO a))
    SetRef :: MutableReference (Ref.IORef a :-> a :-> Full (IO ()))

instance Render MutableReference
  where
    render NewRef = "newRef"
    render GetRef = "getRef"
    render SetRef = "setRef"

instance ToTree MutableReference

instance Eval MutableReference
  where
    evaluate NewRef = fromEval Ref.newIORef
    evaluate GetRef = fromEval Ref.readIORef
    evaluate SetRef = fromEval Ref.writeIORef

instance ExprEq MutableReference
  where
    exprEq NewRef NewRef = True
    exprEq GetRef GetRef = True
    exprEq SetRef SetRef = True
    exprEq _      _      = False

    exprHash NewRef = hashInt 0
    exprHash GetRef = hashInt 1
    exprHash SetRef = hashInt 2

instance WitnessCons MutableReference
  where
    witnessCons NewRef   = ConsWit
    witnessCons GetRef   = ConsWit
    witnessCons SetRef   = ConsWit

instance MaybeWitnessSat ctx MutableReference
  where
    maybeWitnessSat _ _ = Nothing

instance EvalBind MutableReference where evalBindFeat = evalBindFeatDefault

instance (MutableReference :<: dom, Optimize dom ctx dom) =>
    Optimize MutableReference ctx dom
  where
    optimizeFeat = optimizeFeatDefault

type Ref a = Ref.IORef a

instance Show (Ref a)
  where
    show _ = "ref"

newRef' :: (MutableReference :<: dom, Typeable a)
        => HOASTF ctx dom a -> HOASTF ctx dom (IO (Ref a))
newRef' a = inject NewRef :$: a

getRef' :: (MutableReference :<: dom, Typeable a)
        => HOASTF ctx dom (Ref a) -> HOASTF ctx dom (IO a)
getRef' r = inject GetRef :$: r

setRef' :: (MutableReference :<: dom, Typeable a)
        => HOASTF ctx dom (Ref a) -> HOASTF ctx dom a -> HOASTF ctx dom (IO ())
setRef' r a = inject SetRef :$: r :$: a

------------------------------------------------------------------
-- Sugared interface
------------------------------------------------------------------
newRef :: ( MutableReference :<: dom
          , MonadF IO :<: dom
          , Typeable a
          , Sat ctx (Ref (Internal a))
          , Internal b ~ Ref (Internal a)
          , Syntactic a (HODomain ctx dom)
          , Syntactic b (HODomain ctx dom)
          )
       => a -> M ctx dom b
newRef = sugarN newRef'

getRef :: ( MutableReference :<: dom
          , MonadF IO :<: dom
          , Internal v ~ Ref (Internal a)
          , Sat ctx (Internal a)
          , Syntactic a (HODomain ctx dom)
          , Syntactic v (HODomain ctx dom)
          )
       => v -> M ctx dom a
getRef = sugarN getRef'

setRef :: ( MutableReference :<: dom
          , MonadF IO :<: dom
          , Internal v ~ Ref (Internal a)
          , Internal u ~ ()
          , Sat ctx ()
          , Sat ctx (Internal a)
          , Syntactic a (HODomain ctx dom)
          , Syntactic v (HODomain ctx dom)
          , Syntactic u (HODomain ctx dom)
          )
       => v -> a -> M ctx dom u
setRef = sugarN setRef'

modifyRef :: ( MutableReference :<: dom
             , MonadF IO :<: dom
             , Internal v ~ Ref (Internal a)
             , Internal u ~ ()
             , Sat ctx ()
             , Sat ctx (Internal a)
             , Syntactic a (HODomain ctx dom)
             , Syntactic v (HODomain ctx dom)
             , Syntactic u (HODomain ctx dom)
             )
          => v -> (a -> a) -> M ctx dom u
modifyRef r f = getRef r >>= setRef r . f

