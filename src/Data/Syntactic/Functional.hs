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
    , DenotationM
    , liftDenotationM
    , EvalEnv
    , Eval (..)
    , compileSymDen
    , evalOpen
    , eval
    , appDen
    ) where



import Control.Monad.Identity
import Data.Dynamic
import Data.Tree

import Data.Hash (hashInt)
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
    Construct :: Signature sig => String -> Denotation sig -> Construct sig

instance Render Construct
  where
    renderSym (Construct name _) = name
    renderArgs = renderArgsSmart

instance Equality Construct
  where
    equal = equalDefault
    hash  = hashDefault

instance StringTree Construct

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

-- | Mapping from a symbol signature
--
-- > a :-> b :-> Full c
--
-- to
--
-- > m a -> m b -> m c
type family   DenotationM (m :: * -> *) sig
type instance DenotationM m (Full a)    = m a
type instance DenotationM m (a :-> sig) = m a -> DenotationM m sig

-- | Lift a 'Denotation' to 'DenotationM'
liftDenotationM :: forall m sig proxy1 proxy2 . (Monad m, Signature sig) =>
    proxy1 m -> proxy2 sig -> Denotation sig -> DenotationM m sig
liftDenotationM _ _ = help2 sig . help1 sig
  where
    sig = signature :: SigRep sig

    help1 :: Monad m =>
        SigRep sig' -> Denotation sig' -> Args (WrapFull m) sig' -> m (DenResult sig')
    help1 Nil f _ = return f
    help1 (_ :* sig) f (WrapFull ma :* as) = do
        a <- ma
        help1 sig (f a) as

    help2 :: SigRep sig' -> (Args (WrapFull m) sig' -> m (DenResult sig')) -> DenotationM m sig'
    help2 Nil f = f Nil
    help2 (_ :* sig) f = \a -> help2 sig (\as -> f (WrapFull a :* as))

-- | Variable environment used for evaluation
type EvalEnv = [(Name, Dynamic)]
  -- TODO Use a more efficient data structure

class Eval sym env
  where
    compileSym :: proxy env -> sym sig -> DenotationM ((->) env) sig

-- | Simple implementation of `compileSym` from a 'Denotation'
compileSymDen :: forall env sig proxy1 proxy2 . Signature sig =>
    proxy1 env -> proxy2 sig -> Denotation sig -> DenotationM ((->) env) sig
compileSymDen _ p d = liftDenotationM (Proxy :: Proxy ((->) env)) p d

instance (Eval sym1 env, Eval sym2 env) => Eval (sym1 :+: sym2) env
  where
    compileSym p (InjL s) = compileSym p s
    compileSym p (InjR s) = compileSym p s

instance Eval Empty env
  where
    compileSym = error "Not implemented: compileSym for Empty"

instance Eval sym env => Eval (sym :&: info) env
  where
    compileSym p = compileSym p . decorExpr

instance Eval Construct env
  where
    compileSym _ s@(Construct _ d :: Construct sig) = liftDenotationM p s d
      where
        p = Proxy :: Proxy ((->) env)

instance Eval BindingT EvalEnv
  where
    compileSym _ (VarT v) = \env -> case fromJustNote (msgVar v) $ lookup v env of
        d -> fromJustNote msgType $ fromDynamic d
      where
        msgVar v = "evalSem: Variable " ++ show v ++ " not in scope"
        msgType  = "evalSem: type error"  -- TODO Print types
    compileSym _ (LamT v) = \body env a -> body ((v, toDyn a) : env)

-- | \"Compile\" a term to a Haskell function
compile :: Eval sym env => proxy env -> AST sym sig -> DenotationM ((->) env) sig
compile p (Sym s)  = compileSym p s
compile p (s :$ a) = compile p s $ compile p a

-- | Evaluation of open terms
evalOpen :: Eval sym EvalEnv => EvalEnv -> ASTF sym a -> a
evalOpen env a = compile Proxy a env

-- | Evaluation of closed terms
--
-- (Note that there is no guarantee that the term is actually closed.)
eval :: Eval sym EvalEnv => ASTF sym a -> a
eval a = compile (Proxy :: Proxy EvalEnv) a []

-- | Apply a semantic function to a list of arguments
--
-- Can be useful when using 'fold' to evaluate a term.
appDen :: Denotation sig -> Args Identity sig -> DenResult sig
appDen a Nil       = a
appDen f (a :* as) = appDen (f $ result $ runIdentity a) as

