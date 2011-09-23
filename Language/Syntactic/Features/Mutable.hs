{-# LANGUAGE UndecidableInstances #-}

module Language.Syntactic.Features.Mutable
  ( Mutable(..)
  , M
  , runMutable
  )
where

import Language.Syntactic
import Language.Syntactic.Features.Monad
import Language.Syntactic.Features.Binding
import Language.Syntactic.Features.Binding.HigherOrder
import Language.Syntactic.Features.Binding.Optimize

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

instance EvalBind Mutable where evalBindFeat = evalBindFeatDefault

instance (Mutable :<: dom, Optimize dom ctx dom) =>
    Optimize Mutable ctx dom
  where
    optimizeFeat = optimizeFeatDefault

type M ctx dom a = MonadS ctx dom IO a

runMutable' :: forall ctx dom a
            .  (Mutable :<: dom, Typeable a)
            => HOASTF ctx dom (IO a) -> HOASTF ctx dom a
runMutable' ma = inject Run :$: (ma :: HOASTF ctx dom (IO a))

------------------------------------------------------------------
-- Sugared interface
------------------------------------------------------------------
runMutable :: forall ctx dom a
           .  ( Mutable :<: dom
              , MonadF IO :<: dom
              , Sat ctx (Internal a)
              , Syntactic a (HODomain ctx dom)
              )
           => M ctx dom a -> a
runMutable ma = sugar $ inject Run :$: desugar (ma :: M ctx dom a)

