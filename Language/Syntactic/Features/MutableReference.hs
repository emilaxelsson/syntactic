{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Features.MutableReference
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

