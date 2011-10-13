{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Constructs.Mutable
where

import Language.Syntactic
import Language.Syntactic.Constructs.Monad
import Language.Syntactic.Constructs.Binding
import Language.Syntactic.Constructs.Binding.HigherOrder
import Language.Syntactic.Constructs.Binding.Optimize

import System.IO.Unsafe
import Data.Typeable
import Data.Hash

data Mutable a
  where
    Run    :: Mutable (IO a :-> Full a)

instance Render Mutable
  where
    render Run    = "runMutable"

instance ToTree Mutable

instance Eval Mutable
  where
    evaluate Run    = fromEval $ unsafePerformIO

instance ExprEq Mutable
  where
    exprEq Run Run    = True

    exprHash Run = hashInt 0

instance WitnessCons Mutable
  where
    witnessCons Run = ConsWit

instance MaybeWitnessSat ctx Mutable
  where
    maybeWitnessSat _ _ = Nothing

instance EvalBind Mutable where evalBindSym = evalBindSymDefault

instance (Mutable :<: dom, Optimize dom ctx dom) =>
    Optimize Mutable ctx dom
  where
    optimizeSym = optimizeSymDefault

type M ctx dom a = MonadS ctx dom IO a

