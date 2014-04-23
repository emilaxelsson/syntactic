{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Basics for implementing functional EDSLs

module Data.Syntactic.Functional
    ( -- * Syntactic constructs
      Name (..)
    , Construct (..)
    , Binding (..)
    , maxLam
    , lam
    , BindingT (..)
    , maxLamT
    , lamT
    , BindingDomain (..)
      -- * Simple evaluation
    , Denotation
    , EvalEnv
    , Sem (..)
    , evalSem
    , Eval (..)
    , toSem
    , evalOpen
    , evalClosed
    , eval
    , appDen
      -- * Monadic evaluation
    , NonFun (..)
    , FunWit (..)
    , Monadic
    , Monadic1
    , DenotationM
    , DenotationMM
    , MonadicRes
    , getResult
    , appDenM
    , appDenMM
    , SemM (..)
    , evalSemM
    , EvalM (..)
    , toSemM
    , evalOpenM
    , evalClosedM
    , evalM
    ) where



import Control.Monad.Identity
import Data.Tree

import Data.Hash (hashInt)
import Safe

import Data.Syntactic
import Data.Syntactic.TypeUniverse



----------------------------------------------------------------------------------------------------
-- * Syntactic constructs
----------------------------------------------------------------------------------------------------

-- | Generic N-ary syntactic construct
--
-- 'Construct' gives a quick way to introduce a syntactic construct by giving its name and semantic
-- function.
data Construct a
  where
    Construct :: String -> Denotation sig -> Construct sig

instance Render Construct
  where
    renderSym (Construct name _) = name
    renderArgs = renderArgsSmart

instance Equality Construct
  where
    equal = equalDefault
    hash  = hashDefault

instance StringTree Construct

instance Eval Construct t
  where
    toSemSym (Construct _ d) = Sem d

-- | Variable name
newtype Name = Name Integer
  deriving (Eq, Ord, Num)

instance Show Name
  where
    show (Name n) = show n

-- | Variables and binding
data Binding a
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

instance Equality Binding
  where
    equal (Var v1) (Var v2) = v1==v2
    equal (Lam v1) (Lam v2) = v1==v2
    equal _ _ = False

    hash (Var _) = hashInt 0
    hash (Lam _) = hashInt 0

instance Render Binding
  where
    renderSym (Var v) = 'v' : show v
    renderSym (Lam v) = "Lam v" ++ show v
    renderArgs []     (Var v) = 'v' : show v
    renderArgs [body] (Lam v) = "(\\" ++ ('v':show v) ++ " -> " ++ body ++ ")"

instance StringTree Binding
  where
    stringTreeSym []     (Var v) = Node ('v' : show v) []
    stringTreeSym [body] (Lam v) = Node ("Lam " ++ 'v' : show v) [body]

-- | Get the highest variable name of the closest 'Lam' binders. If the term has
-- /ordered binders/ \[1\], 'maxLam' returns the highest name introduced in the whole term.
--
-- \[1\] Ordered binders means that the names of 'Lam' nodes are decreasing along every path from
-- the root.
maxLam :: (Binding :<: s) => AST s a -> Name
maxLam (Sym lam :$ _) | Just (Lam v) <- prj lam = v
maxLam (s :$ a) = maxLam s `Prelude.max` maxLam a
maxLam _ = 0

-- | Higher-order interface for variable binding
--
-- Assumptions:
--
--   * The body @f@ does not inspect its argument.
--
--   * Applying @f@ to a term with ordered binders results in a term with /ordered binders/ \[1\].
--
-- \[1\] Ordered binders means that the names of 'Lam' nodes are decreasing along every path from
-- the root.
lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = appSym (Lam v) body
  where
    body = f (appSym (Var v))
    v    = maxLam body + 1
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)

-- | Typed variables and binding
data BindingT t a
  where
    VarT :: TypeRep t a -> Name -> BindingT t (Full a)
    LamT :: TypeRep t a -> Name -> BindingT t (b :-> Full (a -> b))

instance Equality (BindingT t)
  where
    equal (VarT _ v1) (VarT _ v2) = v1==v2
    equal (LamT _ v1) (LamT _ v2) = v1==v2
    equal _ _ = False

    hash (VarT _ _) = hashInt 0
    hash (LamT _ _) = hashInt 0

instance Render (BindingT t)
  where
    renderSym (VarT _ v) = renderSym (Var v)
    renderSym (LamT _ v) = renderSym (Lam v)
    renderArgs args (VarT _ v) = renderArgs args (Var v)
    renderArgs args (LamT _ v) = renderArgs args (Lam v)

instance StringTree (BindingT t)
  where
    stringTreeSym args (VarT _ v) = stringTreeSym args (Var v)
    stringTreeSym args (LamT _ v) = stringTreeSym args (Lam v)

instance Eval (BindingT t) t
  where
    toSemSym (VarT t v) = SemVar t v
    toSemSym (LamT t v) = SemLam t v

-- | Get the highest variable name of the closest 'LamT' binders. If the term has
-- /ordered binders/ \[1\], 'maxLamT' returns the highest name introduced in the whole term.
--
-- \[1\] Ordered binders means that the names of 'LamT' nodes are decreasing along every path from
-- the root.
maxLamT :: forall t s a . (BindingT t :<: s) => Proxy t -> AST s a -> Name
maxLamT _ (Sym lam :$ _) | Just (LamT _ n :: BindingT t (b :-> a)) <- prj lam = n
maxLamT p (s :$ a) = maxLamT p s `Prelude.max` maxLamT p a
maxLamT _ _ = 0

-- | Higher-order interface for typed variable binding
--
-- Assumptions:
--
--   * The body @f@ does not inspect its argument.
--
--   * Applying @f@ to a term with ordered binders results in a term with /ordered binders/ \[1\].
--
-- \[1\] Ordered binders means that the names of 'LamT' nodes are decreasing along every path from
-- the root.
lamT :: forall t s a b . (BindingT t :<: s, Typeable t a) =>
    Proxy t -> (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lamT p f = appSym (LamT t v :: BindingT t (b :-> Full (a -> b))) body
  where
    t    = typeRep :: TypeRep t a
    body = f (appSym (VarT t v))
    v    = maxLamT p body + 1
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)

-- | Domains that \"might\" include variables and binders
class BindingDomain sym
  where
    prVar :: sym sig -> Maybe Name
    prLam :: sym sig -> Maybe Name
  -- It is in principle possible to replace a constraint `BindingDomain s` by
  -- `(Project Binding s, Project (BindingT t) s)`. However, the problem is that one then has to
  -- specify the type `t` through a `Proxy`. The `BindingDomain` class gets around this problem.

instance (BindingDomain sym1, BindingDomain sym2) => BindingDomain (sym1 :+: sym2)
  where
    prVar (InjL s) = prVar s
    prVar (InjR s) = prVar s
    prLam (InjL s) = prLam s
    prLam (InjR s) = prVar s

instance BindingDomain sym => BindingDomain (sym :&: i)
  where
    prVar = prVar . decorExpr
    prLam = prLam . decorExpr

instance BindingDomain sym => BindingDomain (AST sym)
  where
    prVar (Sym s) = prVar s
    prVar _       = Nothing
    prLam (Sym s) = prVar s
    prLam _       = Nothing

instance BindingDomain Binding
  where
    prVar (Var v) = Just v
    prVar _       = Nothing
    prLam (Lam v) = Just v
    prLam _       = Nothing

instance BindingDomain (BindingT t)
  where
    prVar (VarT _ v) = Just v
    prVar _          = Nothing
    prLam (LamT _ v) = Just v
    prLam _          = Nothing

instance BindingDomain sym
  where
    prVar _ = Nothing
    prLam _ = Nothing



----------------------------------------------------------------------------------------------------
-- * Simple evaluation
----------------------------------------------------------------------------------------------------

-- | Semantic function type of the given symbol signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

-- | Variable environment used for evaluation
type EvalEnv t = [(Name, Dynamic t)]
  -- TODO Use a more efficient data structure

-- | Symbols in a semantic tree
data Sem t a
  where
    SemVar :: TypeRep t a -> Name -> Sem t (Full a)
    SemLam :: TypeRep t a -> Name -> Sem t (b :-> Full (a -> b))
    Sem    :: Denotation sig -> Sem t sig

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

instance Eval Empty t
  where
    toSemSym = error "Not implemented: toSemSym for Empty"

instance Eval sym t => Eval (sym :&: info) t
  where
    toSemSym = toSemSym . decorExpr

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
-- be threaded outside of the semantic functions. (This is done by 'appDenM'.)
type family   Monadic1 (m :: * -> *) a
type instance Monadic1 m (NonFun a) = a
type instance Monadic1 m (a -> b)   = Monadic m (a -> b)

-- | Monadic semantic function. Like 'Denotation', but wraps the result in a monad, and applies
-- 'Monadic1' to the arguments.
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
appDenM :: (Monad m, DenResult sig ~ NonFun a) =>
    DenotationM m sig -> Args (MonadicRes m) sig -> m a
appDenM d Nil                           = d
appDenM d (MonadicRes IsntFun ma :* as) = ma >>= \a -> appDenM (d a) as
appDenM d (MonadicRes IsFun f    :* as) = appDenM (d f) as

-- | Apply a monadic semantic function to a list of 'MonadicRes' arguments
appDenMM :: (Monad m, DenResult sig ~ NonFun a) =>
    DenotationMM m sig -> Args (MonadicRes m) sig -> m a
appDenMM d Nil                    = d
appDenMM d (MonadicRes _ f :* as) = appDenMM (d f) as

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
    ev (SemM d)  as = MonadicRes IsntFun $ appDenM d  $ mapArgs (evalSemM' env) as
    ev (SemMM d) as = MonadicRes IsntFun $ appDenMM d $ mapArgs (evalSemM' env) as

-- | Evaluation of a monadic semantic tree
evalSemM :: (Monad m, TypeEq t t) => EvalEnv t -> ASTF (SemM m t) a -> Monadic m a
evalSemM env = getResult . evalSemM' env

class EvalM sym m t
  where
    toSemSymM :: sym sig -> SemM m t sig

instance (EvalM sym1 m t, EvalM sym2 m t) => EvalM (sym1 :+: sym2) m t
  where
    toSemSymM (InjL s) = toSemSymM s
    toSemSymM (InjR s) = toSemSymM s

instance EvalM Empty t m
  where
    toSemSymM = error "Not implemented: toSemSymM for Empty"

instance EvalM sym t m => EvalM (sym :&: info) t m
  where
    toSemSymM = toSemSymM . decorExpr

-- | Construct a monadic semantic tree
toSemM :: EvalM sym m t => AST sym sig -> AST (SemM m t) sig
toSemM = mapAST toSemSymM

-- | Monadic evaluation of open terms
evalOpenM :: forall sym m t a . (EvalM sym m t, TypeEq t t, Monad m) =>
    Proxy m -> EvalEnv t -> ASTF sym a -> Monadic m a
evalOpenM _ env
    = evalSemM env
    . (id :: ASTF (SemM m t) a -> ASTF (SemM m t) a)
    . toSemM

-- | Monadic evaluation of closed terms
evalClosedM :: forall sym m t a . (EvalM sym m t, TypeEq t t, Monad m) =>
    Proxy m -> Proxy t -> ASTF sym a -> Monadic m a
evalClosedM _ _
    = evalSemM ([] :: EvalEnv t)
    . (id :: ASTF (SemM m t) a -> ASTF (SemM m t) a)
    . toSemM

-- | Monadic evaluation of terms without variables
evalM :: forall sym m a . (EvalM sym m Empty, Monad m) =>
    Proxy m -> ASTF sym a -> Monadic m a
evalM _
    = evalSemM ([] :: EvalEnv Empty)
    . (id :: ASTF (SemM m Empty) a -> ASTF (SemM m Empty) a)
    . toSemM
  -- See comment to `eval`

