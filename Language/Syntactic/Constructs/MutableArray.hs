{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Constructs.MutableArray
where

import Language.Syntactic
import Language.Syntactic.Syntax
import Language.Syntactic.Constructs.Monad
import Language.Syntactic.Constructs.Mutable
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Binding.Optimize
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

instance EvalBind MutableArray where evalBindSym = evalBindSymDefault

instance (MutableArray :<: dom, Optimize dom ctx dom) =>
    Optimize MutableArray ctx dom
  where
    optimizeSym = optimizeSymDefault

type MArr i a = Arr.IOArray i a

