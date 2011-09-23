{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Features.MutableArray
  ( MutableArray(..)
  , MArr
  , newArr
  , getArr
  , setArr
  , modifyArr
  , getBounds
  )
where

import Language.Syntactic
import Language.Syntactic.Syntax
import Language.Syntactic.Features.Monad
import Language.Syntactic.Features.Mutable
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Features.Binding.Optimize
import qualified Data.Array.IO as Arr

import Data.Typeable
import Data.Hash

data MutableArray a
  where
    NewArr    :: Arr.Ix i => MutableArray ((i, i) :-> a :-> Full (IO (Arr.IOArray i a)))
    GetArr    :: Arr.Ix i => MutableArray (Arr.IOArray i a :-> i :-> Full (IO a))
    SetArr    :: Arr.Ix i => MutableArray (Arr.IOArray i a :-> i :-> a :-> Full (IO ()))
    GetBounds :: Arr.Ix i => MutableArray (Arr.IOArray i a :-> Full (IO (i, i)))

instance Render MutableArray
  where
    render NewArr    = "newMArr"
    render GetArr    = "getMArr"
    render SetArr    = "setMArr"
    render GetBounds = "getBounds"

instance ToTree MutableArray

instance Eval MutableArray
  where
    evaluate NewArr    = fromEval Arr.newArray
    evaluate GetArr    = fromEval Arr.readArray
    evaluate SetArr    = fromEval Arr.writeArray
    evaluate GetBounds = fromEval Arr.getBounds

instance ExprEq MutableArray
  where
    exprEq NewArr    NewArr    = True
    exprEq GetArr    GetArr    = True
    exprEq SetArr    SetArr    = True
    exprEq GetBounds GetBounds = True
    exprEq _         _         = False

    exprHash NewArr    = hashInt 0
    exprHash GetArr    = hashInt 1
    exprHash SetArr    = hashInt 2
    exprHash GetBounds = hashInt 3

instance WitnessCons MutableArray
  where
    witnessCons NewArr    = ConsWit
    witnessCons GetArr    = ConsWit
    witnessCons SetArr    = ConsWit
    witnessCons GetBounds = ConsWit

instance MaybeWitnessSat ctx MutableArray
  where
    maybeWitnessSat _ _ = Nothing

instance EvalBind MutableArray where evalBindFeat = evalBindFeatDefault

instance (MutableArray :<: dom, Optimize dom ctx dom) =>
    Optimize MutableArray ctx dom
  where
    optimizeFeat = optimizeFeatDefault

type MArr i a = Arr.IOArray i a

newArr' :: (MutableArray :<: dom, Typeable a, Typeable i, Arr.Ix i)
        => HOASTF ctx dom (i, i) -> HOASTF ctx dom a -> HOASTF ctx dom (IO (MArr i a))
newArr' ii a = inject NewArr :$: ii :$: a

getArr' :: (MutableArray :<: dom, Typeable a, Typeable i, Arr.Ix i)
        => HOASTF ctx dom (MArr i a) -> HOASTF ctx dom i -> HOASTF ctx dom (IO a)
getArr' r i = inject GetArr :$: r :$: i

setArr' :: (MutableArray :<: dom, Typeable a, Typeable i, Arr.Ix i)
        => HOASTF ctx dom (MArr i a) -> HOASTF ctx dom i -> HOASTF ctx dom a -> HOASTF ctx dom (IO ())
setArr' r i a = inject SetArr :$: r :$: i :$: a

getBounds' :: (MutableArray :<: dom, Typeable a, Typeable i, Arr.Ix i)
           => HOASTF ctx dom (MArr i a) -> HOASTF ctx dom (IO (i, i))
getBounds' r = inject GetBounds :$: r

------------------------------------------------------------------
-- Sugared interface
------------------------------------------------------------------
newArr :: ( MutableArray :<: dom
          , MonadF IO :<: dom
          , Typeable a, Typeable i
          , Arr.Ix i
          , Sat ctx (MArr i (Internal a))
          , Internal b ~ MArr i (Internal a)
          , Internal ii ~ (i, i)
          , Syntactic a (HODomain ctx dom)
          , Syntactic b (HODomain ctx dom)
          , Syntactic ii (HODomain ctx dom)
          )
       => ii -> a -> M ctx dom b
newArr = sugarN newArr'

getArr :: ( MutableArray :<: dom
          , MonadF IO :<: dom
          , Arr.Ix (Internal i)
          , Internal v ~ MArr (Internal i) (Internal a)
          , Sat ctx (Internal a)
          , Syntactic a (HODomain ctx dom)
          , Syntactic v (HODomain ctx dom)
          , Syntactic i (HODomain ctx dom)
          )
       => v -> i -> M ctx dom a
getArr = sugarN getArr'

setArr :: ( MutableArray :<: dom
          , MonadF IO :<: dom
          , Arr.Ix (Internal i)
          , Internal v ~ MArr (Internal i) (Internal a)
          , Internal u ~ ()
          , Sat ctx ()
          , Sat ctx (Internal a)
          , Syntactic i (HODomain ctx dom)
          , Syntactic a (HODomain ctx dom)
          , Syntactic v (HODomain ctx dom)
          , Syntactic u (HODomain ctx dom)
          )
       => v -> i -> a -> M ctx dom u
setArr = sugarN setArr'

getBounds :: ( MutableArray :<: dom
             , SyntacticN f (HOASTF ctx dom (MArr i a) -> HOASTF ctx dom (IO (i, i)))
             , Typeable a
             , Typeable i
             , Arr.Ix i
             )
          => f
getBounds = sugarN getBounds'

modifyArr :: ( MutableArray :<: dom
             , MonadF IO :<: dom
             , Arr.Ix (Internal i)
             , Internal v ~ MArr (Internal i) (Internal a)
             , Internal u ~ ()
             , Sat ctx ()
             , Sat ctx (Internal a)
             , Syntactic i (HODomain ctx dom)
             , Syntactic a (HODomain ctx dom)
             , Syntactic v (HODomain ctx dom)
             , Syntactic u (HODomain ctx dom)
             )
          => v -> i -> (a -> a) -> M ctx dom u
modifyArr a i f = getArr a i >>= setArr a i . f

