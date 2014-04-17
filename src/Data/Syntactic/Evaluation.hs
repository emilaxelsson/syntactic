{-# LANGUAGE UndecidableInstances #-}

module Data.Syntactic.Evaluation where



import Control.Monad.Identity

import Safe

import Data.Syntactic
import Data.Syntactic.TypeUniverse



----------------------------------------------------------------------------------------------------
-- * Variable names
----------------------------------------------------------------------------------------------------

-- | Variable name
newtype Name = Name Integer
  deriving (Eq, Ord, Num)

instance Show Name
  where
    show (Name n) = show n



----------------------------------------------------------------------------------------------------
-- * Simple evaluation
----------------------------------------------------------------------------------------------------

-- | Semantic function type of the given symbol signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

-- | Symbols in a semantic tree
data Sem t a
  where
    SemVar :: TypeRep t a -> Name -> Sem t (Full a)
    SemLam :: TypeRep t a -> Name -> Sem t (b :-> Full (a -> b))
    Sem    :: Denotation sig -> Sem t sig

-- | Variable environment used for evaluation
type EvalEnv t = [(Name, Dynamic t)]
  -- TODO Use a more efficient data structure

-- | Evaluation of a semantic tree
evalSem :: TypeEq t t => EvalEnv t -> AST (Sem t) sig -> Denotation sig
evalSem env (Sym (SemVar t v))
    | Dyn ta a <- fromJustNote (msgVar v) $ lookup v env
    , Dict     <- fromJustNote msgType    $ typeEq t ta
    = a
  where
    msgVar v = "evalSem: Variable " ++ show v ++ " not in scope"
    msgType  = "evalSem: type error"  -- TODO Print types
evalSem env (Sym (SemLam ta v) :$ body) = \a -> evalSem ((v, Dyn ta a) : env) body
evalSem env (Sym (Sem d))               = d
evalSem env (s :$ a)                    = evalSem env s $ evalSem env a

-- | Symbol evaluation
class Eval sym t
  where
    toSemSym :: sym sig -> Sem t sig

instance (Eval sym1 t, Eval sym2 t) => Eval (sym1 :+: sym2) t
  where
    toSemSym (InjL s) = toSemSym s
    toSemSym (InjR s) = toSemSym s

instance Eval sym t => Eval (sym :| pred) t            where toSemSym (C a) = toSemSym a
instance Eval sym t => Eval (sym :|| pred) t           where toSemSym (C' a) = toSemSym a
instance Eval sym t => Eval (SubConstr1 c sym p) t     where toSemSym (SubConstr1 a) = toSemSym a
instance Eval sym t => Eval (SubConstr2 c sym pa pb) t where toSemSym (SubConstr2 a) = toSemSym a
instance               Eval Empty t                    where toSemSym = error "Not implemented: toSemSym for Empty"
instance Eval sym t => Eval (sym :&: info) t           where toSemSym = toSemSym . decorExpr

-- | Construct a semantic tree
toSem :: Eval sym t => AST sym sig -> AST (Sem t) sig
toSem = mapAST toSemSym

-- | Evaluation of open terms
evalOpen :: (Eval sym t, TypeEq t t) => EvalEnv t -> AST sym sig -> Denotation sig
evalOpen env = evalSem env . toSem

-- | Evaluation of closed terms
evalClosed :: forall sym t sig . (Eval sym t, TypeEq t t) =>
    Proxy t -> AST sym sig -> Denotation sig
evalClosed _ = evalSem ([] :: EvalEnv t) . toSem

-- | Evaluation of terms without variables
eval :: Eval sym Empty => AST sym sig -> Denotation sig
eval = evalSem ([] :: EvalEnv Empty) . toSem
  -- No guarantee that the expression does not contain variables. This could be made safer by having
  -- a version of `Sem` with only the `Sem` constructor and another class for constructing such
  -- semantic trees.

-- | Apply a semantic function to a list of arguments
appDen :: Denotation sig -> Args Identity sig -> DenResult sig
appDen a Nil       = a
appDen f (a :* as) = appDen (f $ result $ runIdentity a) as



----------------------------------------------------------------------------------------------------
-- * Monadic evaluation
----------------------------------------------------------------------------------------------------

-- | Non-function
newtype NonFun a = NonFun a
  -- TODO With closed type families this type could probably be avoided.

-- | Witness for non-function or function types
data FunWit a
  where
    IsntFun :: FunWit (NonFun a)
    IsFun   :: FunWit (a -> b)
  -- TODO With closed type families this type could probably be avoided.

-- | Wrap result of a [0..]-ary function in a monad
type family   Monadic (m :: * -> *) a
type instance Monadic m (NonFun a) = m a
type instance Monadic m (a -> b)   = a -> Monadic m b

-- | Wrap result of a [1..]-ary function in a monad
--
-- The reason for not wrapping nullary functions is that the effects of nullary monadic values can
-- be threaded outside of the semantic functions. (This is done by 'appArgsM'.)
type family   Monadic1 (m :: * -> *) a
type instance Monadic1 m (NonFun a) = a
type instance Monadic1 m (a -> b)   = Monadic m (a -> b)

-- | Monadic semantic function. Like 'Denotation', but wraps the result in a monad, and applies
-- `Monadic1 m` to the arguments.
type family   DenotationM (m :: * -> *) sig
type instance DenotationM (m :: * -> *) (Full (NonFun a)) = m a
type instance DenotationM (m :: * -> *) (a :-> sig)       = Monadic1 m a -> DenotationM m sig

-- | Monadic semantic function. Like 'Denotation', but wraps the arguments and result in a monad.
type family   DenotationMM (m :: * -> *) sig
type instance DenotationMM (m :: * -> *) (Full (NonFun a)) = m a
type instance DenotationMM (m :: * -> *) (a :-> sig)       = Monadic m a -> DenotationMM m sig

-- | Monadic evaluation result ('Full'-indexed wrapper around a 'Monadic' value)
data MonadicRes m a
  where
    MonadicRes :: FunWit a -> Monadic m a -> MonadicRes m (Full a)

-- | Unwrap a 'MonadicRes'
getResult :: MonadicRes m (Full a) -> Monadic m a
getResult (MonadicRes _ d) = d

-- | Apply a monadic semantic function to a list of 'MonadicRes' arguments
appArgsM :: (Monad m, DenResult sig ~ NonFun a) =>
    DenotationM m sig -> Args (MonadicRes m) sig -> m a
appArgsM d Nil                           = d
appArgsM d (MonadicRes IsntFun ma :* as) = ma >>= \a -> appArgsM (d a) as
appArgsM d (MonadicRes IsFun f    :* as) = appArgsM (d f) as

-- | Apply a monadic semantic function to a list of 'MonadicRes' arguments
appArgsMM :: (Monad m, DenResult sig ~ NonFun a) =>
    DenotationMM m sig -> Args (MonadicRes m) sig -> m a
appArgsMM d Nil                    = d
appArgsMM d (MonadicRes _ f :* as) = appArgsMM (d f) as

-- | Symbols in a monadic semantic tree
data SemM m t sig
  where
    SemVarM :: TypeRep t a -> Name -> SemM m t (Full (NonFun a))
    SemLamM :: TypeRep t a -> Name -> SemM m t (b :-> Full (a -> b))
    SemM    :: (DenResult sig ~ NonFun a) => DenotationM m sig  -> SemM m t sig
    SemMM   :: (DenResult sig ~ NonFun a) => DenotationMM m sig -> SemM m t sig

evalSemM' :: forall m t a . (Monad m, TypeEq t t) =>
    EvalEnv t -> ASTF (SemM m t) a -> MonadicRes m (Full a)
evalSemM' env = match ev
  where
    ev :: SemM m t sig -> Args (AST (SemM m t)) sig -> MonadicRes m (Full (DenResult sig))
    ev (SemVarM t v) Nil
        | Dyn ta a <- fromJustNote (msgVar v) $ lookup v env
        , Dict     <- fromJustNote msgType    $ typeEq t ta
        = MonadicRes IsntFun $ return a
      where
        msgVar v = "evalSem: Variable " ++ show v ++ " not in scope"
        msgType  = "evalSem: type error"  -- TODO Print types
    ev (SemLamM t v) (body :* Nil) =
        MonadicRes IsFun $ \a -> getResult $ evalSemM' ((v, Dyn t a) : env) body
    ev (SemM d)  as = MonadicRes IsntFun $ appArgsM d  $ mapArgs (evalSemM' env) as
    ev (SemMM d) as = MonadicRes IsntFun $ appArgsMM d $ mapArgs (evalSemM' env) as

evalSemM :: (Monad m, TypeEq t t) => EvalEnv t -> ASTF (SemM m t) a -> Monadic m a
evalSemM env = getResult . evalSemM' env

class EvalM sym m t
  where
    toSemSymM :: sym sig -> SemM m t sig

instance (EvalM sym1 m t, EvalM sym2 m t) => EvalM (sym1 :+: sym2) m t
  where
    toSemSymM (InjL s) = toSemSymM s
    toSemSymM (InjR s) = toSemSymM s

instance EvalM sym t m => EvalM (sym :| pred) t m            where toSemSymM (C a) = toSemSymM a
instance EvalM sym t m => EvalM (sym :|| pred) t m           where toSemSymM (C' a) = toSemSymM a
instance EvalM sym t m => EvalM (SubConstr1 c sym p) t m     where toSemSymM (SubConstr1 a) = toSemSymM a
instance EvalM sym t m => EvalM (SubConstr2 c sym pa pb) t m where toSemSymM (SubConstr2 a) = toSemSymM a
instance                  EvalM Empty t m                    where toSemSymM = error "Not implemented: toSemSymM for Empty"
instance EvalM sym t m => EvalM (sym :&: info) t m           where toSemSymM = toSemSymM . decorExpr

-- | Construct a monadic semantic tree
toSemM :: EvalM sym m t => AST sym sig -> AST (SemM m t) sig
toSemM = mapAST toSemSymM

-- | Monadic evaluation of open terms
evalOpenM :: forall sym m t a . (EvalM sym m t, TypeEq t t, Monad m) =>
    EvalEnv t -> ASTF sym a -> Monadic m a
evalOpenM env
    = evalSemM env
    . (id :: ASTF (SemM m t) a -> ASTF (SemM m t) a)
    . toSemM

-- | Evaluation of closed terms
evalM :: forall sym m t a . (EvalM sym m t, TypeEq t t, Monad m) =>
    Proxy t -> ASTF sym a -> Monadic m a
evalM _
    = evalSemM ([] :: EvalEnv t)
    . (id :: ASTF (SemM m t) a -> ASTF (SemM m t) a)
    . toSemM

