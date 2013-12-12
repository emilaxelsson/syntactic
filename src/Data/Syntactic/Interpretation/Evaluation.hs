module Data.Syntactic.Interpretation.Evaluation where



import Control.Monad.Identity

import Data.Syntactic.Syntax
import Data.Syntactic.Traversal



-- | The denotation of a symbol with the given signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

-- | Apply a symbol denotation to a list of arguments
appDen :: Denotation sig -> Args Identity sig -> DenResult sig
appDen a Nil       = a
appDen f (a :* as) = appDen (f $ result $ runIdentity a) as

class Eval expr
  where
    -- | Evaluation of expressions
    evaluate :: expr a -> Denotation a

instance Eval sym => Eval (AST sym)
  where
    evaluate (Sym s)  = evaluate s
    evaluate (s :$ a) = evaluate s $ evaluate a

instance (Eval sym1, Eval sym2) => Eval (sym1 :+: sym2)
  where
    evaluate (InjL a) = evaluate a
    evaluate (InjR a) = evaluate a

