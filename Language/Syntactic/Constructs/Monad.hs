-- | Monadic constructs

module Language.Syntactic.Constructs.Monad where



import Control.Monad

import Language.Syntactic
import Language.Syntactic.Constructs.Symbol

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

instance Monad m => IsSymbol (MONAD m)
  where
    toSym Return = Sym "return" return
    toSym Bind   = Sym "bind"   (>>=)
    toSym Then   = Sym "then"   (>>)
    toSym When   = Sym "when"   when

instance Monad m => ExprEq (MONAD m) where exprEq = exprEqSym; exprHash = exprHashSym
instance Monad m => Render (MONAD m) where renderPart = renderPartSym
instance Monad m => Eval   (MONAD m) where evaluate   = evaluateSym
instance Monad m => ToTree (MONAD m)

-- | Projection with explicit monad type
prjMonad :: (MONAD m :<: sup) => Proxy (m ()) -> sup a -> Maybe (MONAD m a)
prjMonad _ = project

