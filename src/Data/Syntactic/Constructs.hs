{-# LANGUAGE TemplateHaskell #-}

-- | Basic syntactic constructs

module Data.Syntactic.Constructs
    ( Name (..)
    , Construct (..)
    , Binding (..)
    , maxLam
    , lam
    ) where



import Data.Tree

import Data.Syntactic
import Data.Syntactic.Evaluation



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

-- | Variables and binding
data Binding a
  where
    Var :: Name -> Binding (Full a)
    Lam :: Name -> Binding (b :-> Full (a -> b))

instance Render Binding
  where
    renderSym (Var n) = 'v' : show n
    renderSym (Lam n) = "Lam v" ++ show n
    renderArgs []     (Var n) = 'v' : show n
    renderArgs [body] (Lam n) = "(\\" ++ ('v':show n) ++ " -> " ++ body ++ ")"

instance StringTree Binding
  where
    stringTreeSym []     (Var n) = Node ('v' : show n) []
    stringTreeSym [body] (Lam n) = Node ("Lam " ++ 'v' : show n) [body]

-- | Get the highest variable name of the closest 'Lam' binders
maxLam :: (Binding :<: s) => AST s a -> Name
maxLam (Sym lam :$ _) | Just (Lam n) <- prj lam = n
maxLam (s :$ a) = maxLam s `Prelude.max` maxLam a
maxLam _ = 0

-- | Higher-order interface for variable binding
lam :: (Binding :<: s) => (ASTF s a -> ASTF s b) -> ASTF s (a -> b)
lam f = appSym (Lam n) body
  where
    body = f (appSym (Var n))
    n    = maxLam body + 1
  -- Based on "Using Circular Programs for Higher-Order Syntax"
  -- (ICFP 2013, <http://www.cse.chalmers.se/~emax/documents/axelsson2013using.pdf>)

