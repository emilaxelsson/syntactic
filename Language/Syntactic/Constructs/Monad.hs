-- | Monadic constructs

module Language.Syntactic.Constructs.Monad where



import Control.Monad

import Language.Syntactic
import Language.Syntactic.Interpretation.Semantics

import Data.Proxy



data MONAD m a
  where
    Return :: MONAD m (a    :-> Full (m a))
    Bind   :: MONAD m (m a  :-> (a -> m b) :-> Full (m b))
    Then   :: MONAD m (m a  :-> m b        :-> Full (m b))
    When   :: MONAD m (Bool :-> m ()       :-> Full (m ()))

instance WitnessCons (MONAD m)
  where
    witnessCons Return = ConsWit
    witnessCons Bind   = ConsWit
    witnessCons Then   = ConsWit
    witnessCons When   = ConsWit

instance MaybeWitnessSat ctx (MONAD m)
  where
    maybeWitnessSat _ _ = Nothing

instance Monad m => Semantic (MONAD m)
  where
    semantics Return = Sem "return" return
    semantics Bind   = Sem "bind"   (>>=)
    semantics Then   = Sem "then"   (>>)
    semantics When   = Sem "when"   when

instance Monad m => ExprEq (MONAD m) where exprEq = exprEqSem; exprHash = exprHashSem
instance Monad m => Render (MONAD m) where renderPart = renderPartSem
instance Monad m => Eval   (MONAD m) where evaluate   = evaluateSem
instance Monad m => ToTree (MONAD m)

-- | Projection with explicit monad type
prjMonad :: (MONAD m :<: sup) => Proxy (m ()) -> sup a -> Maybe (MONAD m a)
prjMonad _ = prj

