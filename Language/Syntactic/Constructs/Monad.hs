-- | Monadic constructs
--
-- This module is based on the paper
-- /Generic Monadic Constructs for Embedded Languages/ (Persson et al., IFL 2011
-- <http://www.cse.chalmers.se/~emax/documents/persson2011generic.pdf>).

module Language.Syntactic.Constructs.Monad where



import Control.Monad

import Language.Syntactic

import Data.Proxy



data MONAD m sig
  where
    Return :: MONAD m (a    :-> Full (m a))
    Bind   :: MONAD m (m a  :-> (a -> m b) :-> Full (m b))
    Then   :: MONAD m (m a  :-> m b        :-> Full (m b))
    When   :: MONAD m (Bool :-> m ()       :-> Full (m ()))

instance Constrained (MONAD m)
  where
    type Sat (MONAD m) = Top
    exprDict _ = Dict

instance Monad m => Semantic (MONAD m)
  where
    semantics Return = Sem "return" return
    semantics Bind   = Sem "bind"   (>>=)
    semantics Then   = Sem "then"   (>>)
    semantics When   = Sem "when"   when

instance Monad m => Equality (MONAD m) where equal = equalDefault; exprHash = exprHashDefault
instance Monad m => Render   (MONAD m) where renderArgs = renderArgsDefault
instance Monad m => Eval     (MONAD m) where evaluate   = evaluateDefault
instance Monad m => ToTree   (MONAD m)

-- | Projection with explicit monad type
prjMonad :: (MONAD m :<: sup) => Proxy (m ()) -> sup sig -> Maybe (MONAD m sig)
prjMonad _ = prj

