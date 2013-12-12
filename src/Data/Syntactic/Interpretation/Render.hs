module Data.Syntactic.Interpretation.Render
    ( Render (..)
    , render
    , StringTree (..)
    , stringTree
    , showAST
    , drawAST
    ) where



import Data.Tree

import Data.Syntactic.Syntax



-- | Render a symbol as concrete syntax. A complete instance must define at least the 'renderSym'
-- method.
class Render sym
  where
    -- | Show a symbol as a 'String'
    renderSym :: sym sig -> String

    -- | Render a symbol given a list of rendered arguments
    renderArgs :: [String] -> sym sig -> String
    renderArgs []   s = renderSym s
    renderArgs args s = "(" ++ unwords (renderSym s : args) ++ ")"

instance (Render sym1, Render sym2) => Render (sym1 :+: sym2)
  where
    renderSym (InjL s) = renderSym s
    renderSym (InjR s) = renderSym s
    renderArgs args (InjL s) = renderArgs args s
    renderArgs args (InjR s) = renderArgs args s

-- | Render an expression as concrete syntax
render :: forall sym a. Render sym => ASTF sym a -> String
render = go []
  where
    go :: [String] -> AST sym sig -> String
    go args (Sym s)  = renderArgs args s
    go args (s :$ a) = go (render a : args) s

instance Render sym => Show (ASTF sym a)
  where
    show = render



-- | Convert a symbol to a 'Tree' of strings
class Render sym => StringTree sym
  where
    -- | Convert a symbol to a 'Tree' given a list of argument trees
    stringTreeSym :: [Tree String] -> sym a -> Tree String
    stringTreeSym args s = Node (renderSym s) args

instance (StringTree sym1, StringTree sym2) => StringTree (sym1 :+: sym2)
  where
    stringTreeSym args (InjL s) = stringTreeSym args s
    stringTreeSym args (InjR s) = stringTreeSym args s

-- | Convert an expression to a 'Tree' of strings
stringTree :: forall sym a . StringTree sym => ASTF sym a -> Tree String
stringTree = go []
  where
    go :: [Tree String] -> AST sym sig -> Tree String
    go args (Sym s)  = stringTreeSym args s
    go args (s :$ a) = go (stringTree a : args) s

-- | Show a syntax tree using ASCII art
showAST :: StringTree sym => ASTF sym a -> String
showAST = showTree . stringTree

-- | Print a syntax tree using ASCII art
drawAST :: StringTree sym => ASTF sym a -> IO ()
drawAST = putStrLn . showAST

-- | Write a syntax tree to an HTML file with foldable nodes
writeHtmlAST :: StringTree sym => FilePath -> ASTF sym a -> IO ()
writeHtmlAST file = writeHtmlTree file . fmap (\n -> NodeInfo n "") . stringTree

