{-# LANGUAGE DefaultSignatures #-}

module Language.Syntactic.Interpretation.Render
    ( Render (..)
    , renderSymDefault
    , renderArgsDefault
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
import Language.Syntactic.Interpretation.Semantics


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

    default renderSym :: Semantic dom => dom sig -> String
    renderSym = renderSymDefault
    {-# INLINABLE renderSym #-}

-- | Default implementation of 'renderSym'
renderSymDefault :: Semantic expr => expr a -> String
renderSymDefault = renderSym . semantics
{-# INLINABLE renderSymDefault #-}

-- | Default implementation of 'renderArgs'
renderArgsDefault :: Semantic expr => [String] -> expr a -> String
renderArgsDefault args = renderArgs args . semantics
{-# INLINABLE renderArgsDefault #-}

instance Render Semantics
  where
    {-# INLINABLE renderSym #-}
    {-# INLINABLE renderArgs #-}
    renderSym (Sem name _) = name
    renderArgs [] (Sem name _) = name
    renderArgs args (Sem name _)
        | isInfix   = "(" ++ unwords [a,op,b] ++ ")"
        | otherwise = "(" ++ unwords (name : args) ++ ")"
      where
        [a,b] = args
        op    = init $ tail name
        isInfix
          =  not (null name)
          && head name == '('
          && last name == ')'
          && length args == 2

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
writeHtmlAST file = writeHtmlTree Nothing file . fmap (\n -> NodeInfo InitiallyExpanded n "") . stringTree
{-# INLINABLE writeHtmlAST #-}
