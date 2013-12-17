module Language.Syntactic.Interpretation.Render
    ( Render (..)
    , render
    , StringTree (..)
    , stringTree
    , showAST
    , drawAST
    ) where



import Data.Tree

import Language.Syntactic.Syntax



-- | Render an expression as concrete syntax. A complete instance must define
-- either of the methods 'render' and 'renderArgs'.
class Render dom
  where
    -- | Render a symbola as a 'String'
    renderSym :: dom sig -> String

    -- | Render a partially applied expression given a list of rendered missing
    -- arguments
    renderArgs :: [String] -> dom sig -> String
    renderArgs []   a = renderSym a
    renderArgs args a = "(" ++ unwords (renderSym a : args) ++ ")"

render :: forall dom a. Render dom
       => ASTF dom a -> String
render = go []
  where
    go :: [String] -> AST dom sig -> String
    go args (Sym a)  = renderArgs args a
    go args (s :$ a) = go (render a : args) s

instance Render dom => Show (ASTF dom a)
  where
    show = render

instance (Render expr1, Render expr2) => Render (expr1 :+: expr2)
  where
    renderSym (InjL a) = renderSym a
    renderSym (InjR a) = renderSym a
    renderArgs args (InjL a) = renderArgs args a
    renderArgs args (InjR a) = renderArgs args a



class Render dom => StringTree dom
  where
    -- | Convert a partially applied expression to a syntax tree given a list of
    -- rendered missing arguments
    stringTreeSym :: [Tree String] -> dom a -> Tree String
    stringTreeSym args a = Node (renderSym a) args

instance (StringTree dom1, StringTree dom2) => StringTree (dom1 :+: dom2)
  where
    stringTreeSym args (InjL a) = stringTreeSym args a
    stringTreeSym args (InjR a) = stringTreeSym args a

stringTree :: forall dom a . StringTree dom => ASTF dom a -> Tree String
stringTree = go []
  where
    go :: [Tree String] -> AST dom sig -> Tree String
    go args (Sym a)  = stringTreeSym args a
    go args (s :$ a) = go (stringTree a : args) s

-- | Show syntax tree using ASCII art
showAST :: StringTree dom => ASTF dom a -> String
showAST = drawTree . stringTree

-- | Print syntax tree using ASCII art
drawAST :: StringTree dom => ASTF dom a -> IO ()
drawAST = putStrLn . showAST

