{-# LANGUAGE TemplateHaskell #-}

-- | Basic syntactic constructs

module Data.Syntactic.Constructs
    ( Name (..)
    , Construct (..)
    , Binding (..)
    , maxLam
    , lam
    , BindingT (..)
    , maxLamT
    , lamT
    ) where



import Data.Tree

import Data.Hash (hashInt)

import Data.Syntactic
import Data.Syntactic.TypeUniverse
import Data.Syntactic.Evaluation



----------------------------------------------------------------------------------------------------
-- * Generic syntactic constructs
----------------------------------------------------------------------------------------------------

-- | Generic N-ary syntactic construct
data Construct a
  where
    Construct :: String -> Denotation sig -> Construct sig

instance Render Construct
  where
    renderSym (Construct name _) = name
    renderArgs = renderArgsSmart

interpretationInstances ''Construct

instance Eval Construct t
  where
    toSemSym (Construct _ d) = Sem d



----------------------------------------------------------------------------------------------------
-- * Variable binding
----------------------------------------------------------------------------------------------------

-- | Variables and binding
data Binding a
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

-- | 'equal' does strict identifier comparison; i.e. no alpha equivalence.
--
-- 'exprHash' assigns the same hash to all variables and binders. This is a valid over-approximation
-- that enables the following property:
--
-- @`alphaEq` a b ==> `exprHash` a == `exprHash` b@instance Equality Binding
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

-- | Get the highest variable name of the closest 'Lam' binders
maxLam :: (Binding :<: s) => AST s a -> Name
maxLam (Sym lam :$ _) | Just (Lam v) <- prj lam = v
maxLam (s :$ a) = maxLam s `Prelude.max` maxLam a
maxLam _ = 0

-- | Higher-order interface for variable binding
lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = appSym (Lam v) body
  where
    body = f (appSym (Var v))
    v    = maxLam body + 1
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)



----------------------------------------------------------------------------------------------------
-- * Typed variable binding
----------------------------------------------------------------------------------------------------

-- | Typed variables and binding
data BindingT t a
  where
    VarT :: TypeRep t a -> Name -> BindingT t (Full a)
    LamT :: TypeRep t a -> Name -> BindingT t (b :-> Full (a -> b))

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

-- | Get the highest variable name of the closest 'LamT' binders
maxLamT :: forall t s a . (BindingT t :<: s) => Proxy t -> AST s a -> Name
maxLamT _ (Sym lam :$ _) | Just (LamT _ n :: BindingT t (b :-> a)) <- prj lam = n
maxLamT p (s :$ a) = maxLamT p s `Prelude.max` maxLamT p a
maxLamT _ _ = 0

-- | Higher-order interface for typed variable binding
lamT :: forall t s a b . (BindingT t :<: s, Typeable t a) =>
    Proxy t -> (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lamT p f = appSym (LamT t v :: BindingT t (b :-> Full (a -> b))) body
  where
    t    = typeRep :: TypeRep t a
    body = f (appSym (VarT t v))
    v    = maxLamT p body + 1
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)

