{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}

#ifndef MIN_VERSION_GLASGOW_HASKELL
#define MIN_VERSION_GLASGOW_HASKELL(a,b,c,d) 0
#endif
  -- MIN_VERSION_GLASGOW_HASKELL was introduced in GHC 7.10

#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
{-# LANGUAGE OverlappingInstances #-}
#endif

-- | Basics for implementing functional EDSLs

module Language.Syntactic.Functional
    ( -- * Syntactic constructs
      Name (..)
    , Construct (..)
    , Binding (..)
    , maxLam
    , lam
    , fromDeBruijn
    , BindingT (..)
    , maxLamT
    , lamT
    , BindingDomain (..)
    , MONAD (..)
    , Remon (..)
    , desugarMonad
    , desugarMonadT
      -- * Free and bound variables
    , freeVars
    , allVars
      -- * Alpha-equivalence
    , AlphaEnv
    , alphaEq'
    , alphaEq
      -- * Evaluation
    , Denotation
    , Eval (..)
    , evalDen
    , DenotationM
    , liftDenotationM
    , RunEnv
    , EvalEnv (..)
    , compileSymDefault
    , evalOpen
    , evalClosed
      -- * Well-scoped terms
    , Ext (..)
    , lookEnv
    , BindingWS (..)
    , lamWS
    , evalOpenWS
    , evalClosedWS
    , LiftReader
    , UnReader
    , LowerReader
    , ReaderSym (..)
    , WS
    , fromWS
    , smartWS
    ) where



#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
import Control.Applicative
#endif
import Control.DeepSeq
import Control.Monad.Cont
import Control.Monad.Reader
import Data.Dynamic
import Data.List (genericIndex)
#if MIN_VERSION_GLASGOW_HASKELL(7,10,0,0)
#else
import Data.Proxy  -- Needed by GHC < 7.8
#endif
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Tree

import Data.Hash (hashInt)
import Safe

import Language.Syntactic



----------------------------------------------------------------------------------------------------
-- * Syntactic constructs
----------------------------------------------------------------------------------------------------

-- | Generic N-ary syntactic construct
--
-- 'Construct' gives a quick way to introduce a syntactic construct by giving its name and semantic
-- function.
data Construct sig
  where
    Construct :: Signature sig => String -> Denotation sig -> Construct sig

instance Symbol Construct
  where
    rnfSym (Construct name den) = rnf name `seq` den `seq` ()
    symSig (Construct _ _)      = signature

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
  deriving (Eq, Ord, Num, Enum, Real, Integral, NFData)

instance Show Name
  where
    show (Name n) = show n

-- | Variables and binders
data Binding sig
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

instance Symbol Binding
  where
    rnfSym (Var v) = rnf v
    rnfSym (Lam v) = rnf v
    symSig (Var _) = signature
    symSig (Lam _) = signature

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
-- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>).
lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = smartSym (Lam v) body
  where
    body = f (smartSym (Var v))
    v    = succ $ maxLam body

-- | Convert from a term with De Bruijn indexes to one with explicit names
--
-- In the argument term, variable 'Name's are treated as De Bruijn indexes, and lambda 'Name's are
-- ignored. (Ideally, one should use a different type for De Bruijn terms.)
fromDeBruijn :: (Binding :<: sym) => ASTF sym a -> ASTF sym a
fromDeBruijn = go []
  where
    go :: (Binding :<: sym) => [Name] -> ASTF sym a -> (ASTF sym a)
    go vs var           | Just (Var i) <- prj var = inj $ Var $ genericIndex vs i
    go vs (lam :$ body) | Just (Lam _) <- prj lam = inj (Lam v) :$ body'
      where
        body' = go (v:vs) body
        v     = succ $ maxLam body'
          -- Same trick as in `lam`
    go vs a = gmapT (go vs) a

-- | Typed variables and binders
data BindingT sig
  where
    VarT :: Typeable a => Name -> BindingT (Full a)
    LamT :: Typeable a => Name -> BindingT (b :-> Full (a -> b))

instance Symbol BindingT
  where
    rnfSym (VarT v) = rnf v
    rnfSym (LamT v) = rnf v
    symSig (VarT _) = signature
    symSig (LamT _) = signature

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
maxLamT :: Project BindingT sym => AST sym a -> Name
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
-- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>).
lamT :: forall sym symT a b
    .  ( BindingT :<: sym
       , symT ~ Typed sym
       , Typeable a
       , Typeable b
       )
    => (ASTF symT a -> ASTF symT b) -> ASTF symT (a -> b)
lamT f = smartSymT (LamT v) body
  where
    body = f (smartSymT (VarT v))
    v    = succ $ maxLamT body

-- | Domains that \"might\" include variables and binders
class BindingDomain sym
  where
    prVar :: sym sig -> Maybe Name
    prLam :: sym sig -> Maybe Name
  -- It is in principle possible to replace a constraint `BindingDomain s` by
  -- `(Project Binding s, Project BindingT s)`. However, the problem is that one then has to
  -- specify the type `t` through a `Proxy`. The `BindingDomain` class gets around this problem.

instance {-# OVERLAPPING #-}
         (BindingDomain sym1, BindingDomain sym2) => BindingDomain (sym1 :+: sym2)
  where
    prVar (InjL s) = prVar s
    prVar (InjR s) = prVar s
    prLam (InjL s) = prLam s
    prLam (InjR s) = prLam s

instance {-# OVERLAPPING #-} BindingDomain sym => BindingDomain (Typed sym)
  where
    prVar (Typed s) = prVar s
    prLam (Typed s) = prLam s

instance {-# OVERLAPPING #-} BindingDomain sym => BindingDomain (sym :&: i)
  where
    prVar = prVar . decorExpr
    prLam = prLam . decorExpr

instance {-# OVERLAPPING #-} BindingDomain sym => BindingDomain (AST sym)
  where
    prVar (Sym s) = prVar s
    prVar _       = Nothing
    prLam (Sym s) = prLam s
    prLam _       = Nothing

instance {-# OVERLAPPING #-} BindingDomain Binding
  where
    prVar (Var v) = Just v
    prVar _       = Nothing
    prLam (Lam v) = Just v
    prLam _       = Nothing

instance {-# OVERLAPPING #-} BindingDomain BindingT
  where
    prVar (VarT v) = Just v
    prVar _        = Nothing
    prLam (LamT v) = Just v
    prLam _        = Nothing

instance {-# OVERLAPPING #-} BindingDomain sym
  where
    prVar _ = Nothing
    prLam _ = Nothing

-- | Monadic constructs
--
-- See \"Generic Monadic Constructs for Embedded Languages\" (Persson et al., IFL 2011
-- <http://www.cse.chalmers.se/~emax/documents/persson2011generic.pdf>).
data MONAD m sig
  where
    Return :: MONAD m (a :-> Full (m a))
    Bind   :: MONAD m (m a :-> (a -> m b) :-> Full (m b))

instance Symbol (MONAD m)
  where
    symSig Return = signature
    symSig Bind   = signature

instance Render (MONAD m)
  where
    renderSym Return = "return"
    renderSym Bind   = "(>>=)"
    renderArgs = renderArgsSmart

instance Equality (MONAD m)
  where
    equal = equalDefault
    hash  = hashDefault

instance StringTree (MONAD m)

-- | Reifiable monad
--
-- See \"Generic Monadic Constructs for Embedded Languages\" (Persson et al., IFL 2011
-- <http://www.cse.chalmers.se/~emax/documents/persson2011generic.pdf>).
--
-- It is advised to convert to/from 'Mon' using the 'Syntactic' instance provided in the modules
-- @Data.Syntactic.Sugar.Monad@ or @Data.Syntactic.Sugar.MonadT@.
newtype Remon sym m a
  where
    Remon
        :: { unRemon :: forall r . (Monad m, Typeable r)
                     => Cont (ASTF sym (m r)) a
           }
        -> Remon sym m a
  deriving (Functor)
  -- The `Typeable` constraint is a bit unfortunate. It's only needed when using
  -- a `Typed` domain. Since this is probably the most common case I decided to
  -- bake in `Typeable` here. A more flexible solution would be to parameterize
  -- `Remon` on the constraint.

instance (Applicative m) => Applicative (Remon sym m)
  where
    pure a  = Remon $ pure a
    f <*> a = Remon $ unRemon f <*> unRemon a

instance (Monad m) => Monad (Remon dom m)
  where
    return a = Remon $ return a
    ma >>= f = Remon $ unRemon ma >>= unRemon . f

-- | One-layer desugaring of monadic actions
desugarMonad
    :: ( MONAD m :<: sym
       , Monad m
       , Typeable a
       , Typeable m
       )
    => Remon sym m (ASTF sym a) -> ASTF sym (m a)
desugarMonad = flip runCont (sugarSym Return) . unRemon

-- | One-layer desugaring of monadic actions
desugarMonadT
    :: ( MONAD m :<: sym
       , symT ~ Typed sym
       , Monad m
       , Typeable a
       , Typeable m
       )
    => Remon symT m (ASTF symT a) -> ASTF symT (m a)
desugarMonadT = flip runCont (sugarSymT Return) . unRemon



----------------------------------------------------------------------------------------------------
-- * Free variables
----------------------------------------------------------------------------------------------------

-- | Get the set of free variables in an expression
freeVars :: BindingDomain sym => AST sym sig -> Set Name
freeVars var
    | Just v <- prVar var = Set.singleton v
freeVars (lam :$ body)
    | Just v <- prLam lam = Set.delete v (freeVars body)
freeVars (s :$ a) = Set.union (freeVars s) (freeVars a)
freeVars _ = Set.empty

-- | Get the set of variables (free, bound and introduced by lambdas) in an
-- expression
allVars :: BindingDomain sym => AST sym sig -> Set Name
allVars var
    | Just v <- prVar var = Set.singleton v
allVars (lam :$ body)
    | Just v <- prLam lam = Set.insert v (allVars body)
allVars (s :$ a) = Set.union (allVars s) (allVars a)
allVars _ = Set.empty



----------------------------------------------------------------------------------------------------
-- * Alpha-equivalence
----------------------------------------------------------------------------------------------------

-- | Environment used by 'alphaEq''
type AlphaEnv = [(Name,Name)]

alphaEq' :: (Equality sym, BindingDomain sym) => AlphaEnv -> ASTF sym a -> ASTF sym b -> Bool
alphaEq' env var1 var2
    | Just v1 <- prVar var1
    , Just v2 <- prVar var2
    = case (lookup v1 env, lookup v2 env') of
        (Nothing, Nothing)   -> v1==v2  -- Free variables
        (Just v2', Just v1') -> v1==v1' && v2==v2'
        _                    -> False
  where
    env' = [(v2,v1) | (v1,v2) <- env]
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
-- * Evaluation
----------------------------------------------------------------------------------------------------

-- | Semantic function type of the given symbol signature
type family   Denotation sig
type instance Denotation (Full a)    = a
type instance Denotation (a :-> sig) = a -> Denotation sig

class Eval s
  where
    evalSym :: s sig -> Denotation sig

instance (Eval s, Eval t) => Eval (s :+: t)
  where
    evalSym (InjL s) = evalSym s
    evalSym (InjR s) = evalSym s

instance Eval Empty
  where
    evalSym = error "evalSym: Empty"

instance Eval sym => Eval (sym :&: info)
  where
    evalSym = evalSym . decorExpr

instance Eval Construct
  where
    evalSym (Construct _ d) = d

instance Monad m => Eval (MONAD m)
  where
    evalSym Return = return
    evalSym Bind   = (>>=)

-- | Evaluation
evalDen :: Eval s => AST s sig -> Denotation sig
evalDen = go
  where
    go :: Eval s => AST s sig -> Denotation sig
    go (Sym s)  = evalSym s
    go (s :$ a) = go s $ go a

-- | Monadic denotation; mapping from a symbol signature
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
liftDenotationM :: forall m sig proxy1 proxy2 . Monad m =>
    SigRep sig -> proxy1 m -> proxy2 sig -> Denotation sig -> DenotationM m sig
liftDenotationM sig _ _ = help2 sig . help1 sig
  where
    help1 :: Monad m =>
        SigRep sig' -> Denotation sig' -> Args (WrapFull m) sig' -> m (DenResult sig')
    help1 SigFull f _ = return f
    help1 (SigMore sig) f (WrapFull ma :* as) = do
        a <- ma
        help1 sig (f a) as

    help2 :: SigRep sig' -> (Args (WrapFull m) sig' -> m (DenResult sig')) -> DenotationM m sig'
    help2 SigFull f = f Nil
    help2 (SigMore sig) f = \a -> help2 sig (\as -> f (WrapFull a :* as))

-- | Runtime environment
type RunEnv = [(Name, Dynamic)]
  -- TODO Use a more efficient data structure?

-- | Evaluation
class EvalEnv sym env
  where
    default compileSym :: (Symbol sym, Eval sym) =>
        proxy env -> sym sig -> DenotationM (Reader env) sig

    compileSym :: proxy env -> sym sig -> DenotationM (Reader env) sig
    compileSym p s = compileSymDefault (symSig s) p s

-- | Simple implementation of `compileSym` from a 'Denotation'
compileSymDefault :: forall proxy env sym sig . Eval sym =>
    SigRep sig -> proxy env -> sym sig -> DenotationM (Reader env) sig
compileSymDefault sig p s = liftDenotationM sig (Proxy :: Proxy (Reader env)) s (evalSym s)

instance (EvalEnv sym1 env, EvalEnv sym2 env) => EvalEnv (sym1 :+: sym2) env
  where
    compileSym p (InjL s) = compileSym p s
    compileSym p (InjR s) = compileSym p s

instance EvalEnv Empty env
  where
    compileSym = error "compileSym: Empty"

instance EvalEnv sym env => EvalEnv (Typed sym) env
  where
    compileSym p (Typed s) = compileSym p s

instance EvalEnv sym env => EvalEnv (sym :&: info) env
  where
    compileSym p = compileSym p . decorExpr

instance EvalEnv Construct env
  where
    compileSym _ s@(Construct _ d) = liftDenotationM signature p s d
      where
        p = Proxy :: Proxy (Reader env)

instance Monad m => EvalEnv (MONAD m) env

instance EvalEnv BindingT RunEnv
  where
    compileSym _ (VarT v) = reader $ \env -> case fromJustNote (msgVar v) $ lookup v env of
        d -> fromJustNote msgType $ fromDynamic d
      where
        msgVar v = "compileSym: Variable " ++ show v ++ " not in scope"
        msgType  = "compileSym: type error"  -- TODO Print types
    compileSym _ (LamT v) = \body -> reader $ \env a -> runReader body ((v, toDyn a) : env)

-- | \"Compile\" a term to a Haskell function
compile :: EvalEnv sym env => proxy env -> AST sym sig -> DenotationM (Reader env) sig
compile p (Sym s)  = compileSym p s
compile p (s :$ a) = compile p s $ compile p a
  -- This use of the term \"compile\" comes from \"Typing Dynamic Typing\" (Baars and Swierstra,
  -- ICFP 2002, <http://doi.acm.org/10.1145/581478.581494>)

-- | Evaluation of open terms
evalOpen :: EvalEnv sym env => env -> ASTF sym a -> a
evalOpen env a = runReader (compile Proxy a) env

-- | Evaluation of closed terms where 'RunEnv' is used as the internal environment
--
-- (Note that there is no guarantee that the term is actually closed.)
evalClosed :: EvalEnv sym RunEnv => ASTF sym a -> a
evalClosed a = runReader (compile (Proxy :: Proxy RunEnv) a) []



----------------------------------------------------------------------------------------------------
-- * Well-scoped terms
----------------------------------------------------------------------------------------------------

-- | Environment extension
class Ext ext orig
  where
    -- | Remove the extension of an environment
    unext :: ext -> orig
    -- | Return the amount by which an environment has been extended
    diff :: Num a => Proxy ext -> Proxy orig -> a

instance {-# OVERLAPPING #-} Ext env env
  where
    unext = id
    diff _ _ = 0

instance {-# OVERLAPPING #-} (Ext env e, ext ~ (a,env)) => Ext ext e
  where
    unext = unext . snd
    diff m n = diff (fmap snd m) n + 1

-- | Lookup in an extended environment
lookEnv :: forall env a e . Ext env (a,e) => Proxy e -> Reader env a
lookEnv _ = reader $ \env -> let (a, _ :: e) = unext env in a

-- | Well-scoped variable binding
--
-- Well-scoped terms are introduced to be able to evaluate without type casting. The implementation
-- is inspired by \"Typing Dynamic Typing\" (Baars and Swierstra, ICFP 2002,
-- <http://doi.acm.org/10.1145/581478.581494>) where expressions are represented as (essentially)
-- @`Reader` env a@ after \"compilation\". However, a major difference is that
-- \"Typing Dynamic Typing\" starts from an untyped term, and thus needs (safe) dynamic type casting
-- during compilation. In contrast, the denotational semantics of 'BindingWS' (the 'Eval' instance)
-- uses no type casting.
data BindingWS sig
  where
    VarWS :: Ext env (a,e) => Proxy e -> BindingWS (Full (Reader env a))
    LamWS :: BindingWS (Reader (a,e) b :-> Full (Reader e (a -> b)))

instance Symbol BindingWS
  where
    rnfSym (VarWS Proxy) = ()
    rnfSym LamWS         = ()
    symSig (VarWS _)     = signature
    symSig LamWS         = signature

instance Eval BindingWS
  where
    evalSym (VarWS p) = lookEnv p
    evalSym LamWS     = \f -> reader $ \e -> \a -> runReader f (a,e)

-- | Higher-order interface for well-scoped variable binding
--
-- Inspired by Conor McBride's "I am not a number, I am a classy hack"
-- (<http://mazzo.li/epilogue/index.html%3Fp=773.html>).
lamWS :: forall a e sym b . (BindingWS :<: sym)
    => ((forall env . (Ext env (a,e)) => ASTF sym (Reader env a)) -> ASTF sym (Reader (a,e) b))
    -> ASTF sym (Reader e (a -> b))
lamWS f = smartSym LamWS $ f $ smartSym (VarWS (Proxy :: Proxy e))

-- | Evaluation of open well-scoped terms
evalOpenWS :: Eval s => env -> ASTF s (Reader env a) -> a
evalOpenWS e = ($ e) . runReader . evalDen

-- | Evaluation of closed well-scoped terms
evalClosedWS :: Eval s => ASTF s (Reader () a) -> a
evalClosedWS = evalOpenWS ()

-- | Mapping from a symbol signature
--
-- > a :-> b :-> Full c
--
-- to
--
-- > Reader env a :-> Reader env b :-> Full (Reader env c)
type family   LiftReader env sig
type instance LiftReader env (Full a)    = Full (Reader env a)
type instance LiftReader env (a :-> sig) = Reader env a :-> LiftReader env sig

type family UnReader a
type instance UnReader (Reader e a) = a

-- | Mapping from a symbol signature
--
-- > Reader e a :-> Reader e b :-> Full (Reader e c)
--
-- to
--
-- > a :-> b :-> Full c
type family   LowerReader sig
type instance LowerReader (Full a)    = Full (UnReader a)
type instance LowerReader (a :-> sig) = UnReader a :-> LowerReader sig

-- | Wrap a symbol to give it a 'LiftReader' signature
data ReaderSym sym sig
  where
    ReaderSym
        :: ( Signature sig
           , Denotation (LiftReader env sig) ~ DenotationM (Reader env) sig
           , LowerReader (LiftReader env sig) ~ sig
           )
        => Proxy env
        -> sym sig
        -> ReaderSym sym (LiftReader env sig)

instance Eval sym => Eval (ReaderSym sym)
  where
    evalSym (ReaderSym (_ :: Proxy env) s) = liftDenotationM signature p s $ evalSym s
      where
        p = Proxy :: Proxy (Reader env)

-- | Well-scoped 'AST'
type WS sym env a = ASTF (BindingWS :+: ReaderSym sym) (Reader env a)

-- | Convert the representation of variables and binders from 'BindingWS' to 'Binding'. The latter
-- is easier to analyze, has a 'Render' instance, etc.
fromWS :: WS sym env a -> ASTF (Binding :+: sym) a
fromWS = fromDeBruijn . go
  where
    go :: AST (BindingWS :+: ReaderSym sym) sig -> AST (Binding :+: sym) (LowerReader sig)
    go (Sym (InjL s@(VarWS p)))     = Sym (InjL (Var (diff (mkProxy2 s) (mkProxy1 s p))))
      where
        mkProxy1 = (\_ _ -> Proxy) :: BindingWS (Full (Reader e' a)) -> Proxy e -> Proxy (a,e)
        mkProxy2 = (\_ -> Proxy)   :: BindingWS (Full (Reader e' a)) -> Proxy e'
    go (Sym (InjL LamWS))           = Sym $ InjL $ Lam (-1) -- -1 since we're using De Bruijn
    go (s :$ a)                     = go s :$ go a
    go (Sym (InjR (ReaderSym _ s))) = Sym $ InjR s

-- | Make a smart constructor for well-scoped terms. 'smartWS' has any type of the form:
--
-- > smartWS :: (sub :<: sup, bsym ~ (BindingWS :+: ReaderSym sup))
-- >     => sub (a :-> b :-> ... :-> Full x)
-- >     -> ASTF bsym (Reader env a) -> ASTF bsym (Reader env b) -> ... -> ASTF bsym (Reader env x)
smartWS :: forall sig sig' bsym f sub sup env a
    .  ( Signature sig
       , Signature sig'
       , sub :<: sup
       , bsym ~ (BindingWS :+: ReaderSym sup)
       , f    ~ SmartFun bsym sig'
       , sig' ~ SmartSig f
       , bsym ~ SmartSym f
       , sig' ~ LiftReader env sig
       , Denotation (LiftReader env sig) ~ DenotationM (Reader env) sig
       , LowerReader (LiftReader env sig) ~ sig
       , Reader env a ~ DenResult sig'
       )
    => sub sig -> f
smartWS s = smartSym' $ InjR $ ReaderSym (Proxy :: Proxy env) $ inj s

