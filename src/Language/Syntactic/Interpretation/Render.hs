module Language.Syntactic.Interpretation.Render
    ( Render (..)
    , render
    , StringTree (..)
    , stringTree
    , showAST
    , drawAST
    , writeHtmlAST
    ) where



import Data.Tree (Tree (..))

import Data.Tree.View

import Language.Syntactic.Syntax


-- | Render a symbol as concrete syntax. A complete instance must define at least the 'renderSym'
-- method.
class Render dom
  where
    -- | Show a symbol as a 'String'
    renderSym :: dom sig -> String

    -- | Render a symbol given a list of rendered arguments
    renderArgs :: [String] -> dom sig -> String
    renderArgs []   a = renderSym a
    renderArgs args a = "(" ++ unwords (renderSym a : args) ++ ")"
    {-# INLINABLE renderArgs #-}

instance (Render expr1, Render expr2) => Render (expr1 :+: expr2)
  where
    {-# SPECIALIZE instance (Render expr1, Render expr2) => Render (expr1 :+: expr2) #-}
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (InjL a) = renderSym a
    renderSym (InjR a) = renderSym a
    renderArgs args (InjL a) = renderArgs args a
    renderArgs args (InjR a) = renderArgs args a

-- | Render an expression as concrete syntax
render :: forall dom a. Render dom => ASTF dom a -> String
render = go []
  where
    go :: [String] -> AST dom sig -> String
    go args (Sym a)  = renderArgs args a
    go args (s :$ a) = go (render a : args) s
{-# INLINABLE render #-}

instance Render dom => Show (ASTF dom a)
  where
    {-# SPECIALIZE instance Render dom => Show (ASTF dom a) #-}
    show = render



-- | Convert a symbol to a 'Tree' of strings
class Render dom => StringTree dom
  where
    -- | Convert a symbol to a 'Tree' given a list of argument trees
    stringTreeSym :: [Tree String] -> dom a -> Tree String
    stringTreeSym args a = Node (renderSym a) args
    {-# INLINABLE stringTreeSym #-}

instance (StringTree dom1, StringTree dom2) => StringTree (dom1 :+: dom2)
  where
    {-# SPECIALIZE instance (StringTree dom1, StringTree dom2) => StringTree (dom1 :+: dom2) #-}
    {-# INLINABLE stringTreeSym #-}
    stringTreeSym args (InjL a) = stringTreeSym args a
    stringTreeSym args (InjR a) = stringTreeSym args a

-- | Convert an expression to a 'Tree' of strings
stringTree :: forall dom a . StringTree dom => ASTF dom a -> Tree String
stringTree = go []
  where
    go :: [Tree String] -> AST dom sig -> Tree String
    go args (Sym a)  = stringTreeSym args a
    go args (s :$ a) = go (go [] a : args) s
{-# INLINABLE stringTree #-}

-- | Show a syntax tree using ASCII art
showAST :: StringTree dom => ASTF dom a -> String
showAST = showTree . stringTree
{-# INLINABLE showAST #-}

-- | Print a syntax tree using ASCII art
drawAST :: StringTree dom => ASTF dom a -> IO ()
drawAST = putStrLn . showAST
{-# INLINABLE drawAST #-}

writeHtmlAST :: StringTree sym => FilePath -> ASTF sym a -> IO ()
writeHtmlAST file = writeHtmlTree file . fmap (\n -> NodeInfo n "") . stringTree
{-# INLINABLE writeHtmlAST #-}
