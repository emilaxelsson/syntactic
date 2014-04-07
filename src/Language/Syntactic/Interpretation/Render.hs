{-# LANGUAGE Haskell2010 #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

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

instance (Render expr1, Render expr2) => Render (expr1 :+: expr2)
  where
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

instance Render dom => Show (ASTF dom a)
  where
    show = render



-- | Convert a symbol to a 'Tree' of strings
class Render dom => StringTree dom
  where
    -- | Convert a symbol to a 'Tree' given a list of argument trees
    stringTreeSym :: [Tree String] -> dom a -> Tree String
    stringTreeSym args a = Node (renderSym a) args

instance (StringTree dom1, StringTree dom2) => StringTree (dom1 :+: dom2)
  where
    stringTreeSym args (InjL a) = stringTreeSym args a
    stringTreeSym args (InjR a) = stringTreeSym args a

-- | Convert an expression to a 'Tree' of strings
stringTree :: forall dom a . StringTree dom => ASTF dom a -> Tree String
stringTree = go []
  where
    go :: [Tree String] -> AST dom sig -> Tree String
    go args (Sym a)  = stringTreeSym args a
    go args (s :$ a) = go (stringTree a : args) s

-- | Show a syntax tree using ASCII art
showAST :: StringTree dom => ASTF dom a -> String
showAST = showTree . stringTree

-- | Print a syntax tree using ASCII art
drawAST :: StringTree dom => ASTF dom a -> IO ()
drawAST = putStrLn . showAST

writeHtmlAST :: StringTree sym => FilePath -> ASTF sym a -> IO ()
writeHtmlAST file = writeHtmlTree file . fmap (\n -> NodeInfo n "") . stringTree

