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
      -- * Alpha-equivalence
    , AlphaEnv
    , alphaEq'
    , alphaEq
      -- * Simple evaluation
    , Denotation
    , EvalEnv
    , Sem (..)
    , evalSem
    , Eval (..)
    , toSem
    , evalOpen
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
    , evalM
    ) where



import Control.Monad.Identity
import Data.Tree
import Data.Dynamic

import Data.Hash (hashInt)
import Data.Proxy
import Safe

import Data.Syntactic



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

instance Eval Construct
  where
    toSemSym (Construct _ d) = Sem d

-- | Variable name
newtype Name = Name Integer
  deriving (Eq, Ord, Num, Enum)

instance Show Name
  where
    show (Name n) = show n

-- | Variables and binders
data Binding a
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'hash' assigns the same hash to all variables and binders. This is a valid over-approximation
-- that enables the following property:
--
-- @`alphaEq` a b ==> `hash` a == `hash` b@
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

-- | Get the highest name bound by the first 'Lam' binders at every path from the root. If the term
-- has /ordered binders/ \[1\], 'maxLam' returns the highest name introduced in the whole term.
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
--
-- See \"Using Circular Programs for Higher-Order Syntax\"
-- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)
lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = appSym (Lam v) body
  where
    body = f (appSym (Var v))
    v    = maxLam body + 1

-- | Typed variables and binders
data BindingT a
  where
    VarT :: Typeable a => Name -> BindingT (Full a)
    LamT :: Typeable a => Name -> BindingT (b :-> Full (a -> b))

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'hash' assigns the same hash to all variables and binders. This is a valid over-approximation
-- that enables the following property:
--
-- @`alphaEq` a b ==> `hash` a == `hash` b@
instance Equality BindingT
  where
    equal (VarT v1) (VarT v2) = v1==v2
    equal (LamT v1) (LamT v2) = v1==v2
    equal _ _ = False

    hash (VarT _) = hashInt 0
    hash (LamT _) = hashInt 0

instance Render BindingT
  where
    renderSym (VarT v) = renderSym (Var v)
    renderSym (LamT v) = renderSym (Lam v)
    renderArgs args (VarT v) = renderArgs args (Var v)
    renderArgs args (LamT v) = renderArgs args (Lam v)

instance StringTree BindingT
  where
    stringTreeSym args (VarT v) = stringTreeSym args (Var v)
    stringTreeSym args (LamT v) = stringTreeSym args (Lam v)

instance Eval BindingT
  where
    toSemSym (VarT v) = SemVar v
    toSemSym (LamT v) = SemLam v

-- | Get the highest name bound by the first 'LamT' binders at every path from the root. If the term
-- has /ordered binders/ \[1\], 'maxLamT' returns the highest name introduced in the whole term.
--
-- \[1\] Ordered binders means that the names of 'LamT' nodes are decreasing along every path from
-- the root.
maxLamT :: (BindingT :<: s) => AST s a -> Name
maxLamT (Sym lam :$ _) | Just (LamT n :: BindingT (b :-> a)) <- prj lam = n
maxLamT (s :$ a) = maxLamT s `Prelude.max` maxLamT a
maxLamT _ = 0

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
--
-- See \"Using Circular Programs for Higher-Order Syntax\"
-- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)
lamT :: forall s a b . (BindingT :<: s, Typeable a) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lamT f = appSym (LamT v :: BindingT (b :-> Full (a -> b))) body
  where
    body = f (appSym (VarT v))
    v    = maxLamT body + 1

-- | Domains that \"might\" include variables and binders
class BindingDomain sym
  where
    prVar :: sym sig -> Maybe Name
    prLam :: sym sig -> Maybe Name
  -- It is in principle possible to replace a constraint `BindingDomain s` by
  -- `(Project Binding s, Project BindingT s)`. However, the problem is that one then has to
  -- specify the type `t` through a `Proxy`. The `BindingDomain` class gets around this problem.

instance (BindingDomain sym1, BindingDomain sym2) => BindingDomain (sym1 :+: sym2)
  where
    prVar (InjL s) = prVar s
    prVar (InjR s) = prVar s
    prLam (InjL s) = prLam s
    prLam (InjR s) = prLam s

instance BindingDomain sym => BindingDomain (sym :&: i)
  where
    prVar = prVar . decorExpr
    prLam = prLam . decorExpr

instance BindingDomain sym => BindingDomain (AST sym)
  where
    prVar (Sym s) = prVar s
    prVar _       = Nothing
    prLam (Sym s) = prLam s
    prLam _       = Nothing

instance BindingDomain Binding
  where
    prVar (Var v) = Just v
    prVar _       = Nothing
    prLam (Lam v) = Just v
    prLam _       = Nothing

instance BindingDomain BindingT
  where
    prVar (VarT v) = Just v
    prVar _        = Nothing
    prLam (LamT v) = Just v
    prLam _        = Nothing

instance BindingDomain sym
  where
    prVar _ = Nothing
    prLam _ = Nothing



----------------------------------------------------------------------------------------------------
-- * Alpha-equivalence
----------------------------------------------------------------------------------------------------

-- | Environment used by 'alphaEq''
type AlphaEnv = [(Name,Name)]

alphaEq' :: (Equality sym, BindingDomain sym) => AlphaEnv -> ASTF sym a -> ASTF sym b -> Bool
alphaEq' env var1 var2
    | Just v1 <- prVar var1
    , Just v2 <- prVar var2
    = case lookup v1 env of
        Nothing  -> v1==v2   -- Free variables
        Just v2' -> v2==v2'
alphaEq' env (lam1 :$ body1) (lam2 :$ body2)
    | Just v1 <- prLam lam1
    , Just v2 <- prLam lam2
    = alphaEq' ((v1,v2):env) body1 body2
alphaEq' env a b = simpleMatch (alphaEq'' env b) a

alphaEq'' :: (Equality sym, BindingDomain sym) =>
    AlphaEnv -> ASTF sym b -> sym a -> Args (AST sym) a -> Bool
alphaEq'' env b a aArgs = simpleMatch (alphaEq''' env a aArgs) b

alphaEq''' :: (Equality sym, BindingDomain sym) =>
    AlphaEnv -> sym a -> Args (AST sym) a -> sym b -> Args (AST sym) b -> Bool
alphaEq''' env a aArgs b bArgs
    | equal a b = alphaEqChildren env a' b'
    | otherwise = False
  where
    a' = appArgs (Sym undefined) aArgs
    b' = appArgs (Sym undefined) bArgs

alphaEqChildren :: (Equality sym, BindingDomain sym) => AlphaEnv -> AST sym a -> AST sym b -> Bool
alphaEqChildren _ (Sym _) (Sym _) = True
alphaEqChildren env (s :$ a) (t :$ b) = alphaEqChildren env s t && alphaEq' env a b
alphaEqChildren _ _ _ = False

-- | Alpha-equivalence
alphaEq :: (Equality sym, BindingDomain sym) => ASTF sym a -> ASTF sym b -> Bool
alphaEq = alphaEq' []



----------------------------------------------------------------------------------------------------
-- * Simple evaluation
----------------------------------------------------------------------------------------------------

-- | Semantic function type of the given symbol signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

-- | Variable environment used for evaluation
type EvalEnv = [(Name, Dynamic)]
  -- TODO Use a more efficient data structure

-- | Symbols in a semantic tree
data Sem a
  where
    SemVar :: Typeable a => Name -> Sem (Full a)
    SemLam :: Typeable a => Name -> Sem (b :-> Full (a -> b))
    Sem    :: Denotation sig -> Sem sig

-- | Evaluation of a semantic tree
evalSem :: EvalEnv -> AST Sem sig -> Denotation sig
evalSem env (Sym (SemVar v))
    | d <- fromJustNote (msgVar v) $ lookup v env
    = fromJustNote msgType $ fromDynamic d
  where
    msgVar v = "evalSem: Variable " ++ show v ++ " not in scope"
    msgType  = "evalSem: type error"  -- TODO Print types
evalSem env (Sym (SemLam v) :$ body) = \a -> evalSem ((v, toDyn a) : env) body
evalSem env (Sym (Sem d))            = d
evalSem env (s :$ a)                 = evalSem env s $ evalSem env a

-- | Symbol evaluation
class Eval sym
  where
    toSemSym :: sym sig -> Sem sig

instance (Eval sym1, Eval sym2) => Eval (sym1 :+: sym2)
  where
    toSemSym (InjL s) = toSemSym s
    toSemSym (InjR s) = toSemSym s

instance Eval Empty
  where
    toSemSym = error "Not implemented: toSemSym for Empty"

instance Eval sym => Eval (sym :&: info)
  where
    toSemSym = toSemSym . decorExpr

-- | Construct a semantic tree
toSem :: Eval sym => AST sym sig -> AST Sem sig
toSem = mapAST toSemSym

-- | Evaluation of open terms
evalOpen :: Eval sym => EvalEnv -> AST sym sig -> Denotation sig
evalOpen env = evalSem env . toSem

-- | Evaluation of closed terms
eval :: Eval sym => AST sym sig -> Denotation sig
eval = evalSem []. toSem

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
data SemM m sig
  where
    SemVarM :: Typeable a => Name -> SemM m (Full (NonFun a))
    SemLamM :: Typeable a => Name -> SemM m (b :-> Full (a -> b))
    SemM    :: (DenResult sig ~ NonFun a) => DenotationM m sig  -> SemM m sig
    SemMM   :: (DenResult sig ~ NonFun a) => DenotationMM m sig -> SemM m sig

evalSemM' :: forall m a . Monad m => EvalEnv -> ASTF (SemM m) a -> MonadicRes m (Full a)
evalSemM' env = match ev
  where
    ev :: SemM m sig -> Args (AST (SemM m)) sig -> MonadicRes m (Full (DenResult sig))
    ev (SemVarM v) Nil
        | d <- fromJustNote (msgVar v) $ lookup v env
        = MonadicRes IsntFun $ return $ fromJustNote msgType $ fromDynamic d
      where
        msgVar v = "evalSem: Variable " ++ show v ++ " not in scope"
        msgType  = "evalSem: type error"  -- TODO Print types
    ev (SemLamM v) (body :* Nil) =
        MonadicRes IsFun $ \a -> getResult $ evalSemM' ((v, toDyn a) : env) body
    ev (SemM d)  as = MonadicRes IsntFun $ appDenM d  $ mapArgs (evalSemM' env) as
    ev (SemMM d) as = MonadicRes IsntFun $ appDenMM d $ mapArgs (evalSemM' env) as

-- | Evaluation of a monadic semantic tree
evalSemM :: Monad m => EvalEnv -> ASTF (SemM m) a -> Monadic m a
evalSemM env = getResult . evalSemM' env

class EvalM sym m
  where
    toSemSymM :: sym sig -> SemM m sig

instance (EvalM sym1 m, EvalM sym2 m) => EvalM (sym1 :+: sym2) m
  where
    toSemSymM (InjL s) = toSemSymM s
    toSemSymM (InjR s) = toSemSymM s

instance EvalM Empty m
  where
    toSemSymM = error "Not implemented: toSemSymM for Empty"

instance EvalM sym m => EvalM (sym :&: info) m
  where
    toSemSymM = toSemSymM . decorExpr

-- | Construct a monadic semantic tree
toSemM :: EvalM sym m => AST sym sig -> AST (SemM m) sig
toSemM = mapAST toSemSymM

-- | Monadic evaluation of open terms
evalOpenM :: forall sym m a . (EvalM sym m, Monad m) =>
    Proxy m -> EvalEnv -> ASTF sym a -> Monadic m a
evalOpenM _ env
    = evalSemM env
    . (id :: ASTF (SemM m) a -> ASTF (SemM m) a)
    . toSemM

-- | Monadic evaluation of closed terms
evalM :: forall sym m a . (EvalM sym m, Monad m) => Proxy m -> ASTF sym a -> Monadic m a
evalM _
    = evalSemM []
    . (id :: ASTF (SemM m) a -> ASTF (SemM m) a)
    . toSemM

