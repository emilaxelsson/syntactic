module Language.Syntactic.Interpretation.Render
    ( Render (..)
    , render
    , printExpr
    , ToTree (..)
    , toTree
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

-- | Print an expression
printExpr :: Render dom => ASTF dom a -> IO ()
printExpr = putStrLn . render



-- | Convert an expression to a tree
toTree :: forall dom a b. (forall sig. dom sig -> b) -> ASTF dom a -> Tree b
toTree f = go []
  where
    go :: [Tree b] -> AST dom sig -> Tree b
    go args (Sym a)  = Node (f a) args
    go args (s :$ a) = go (toTree f a : args) s


class Render expr => ToTree expr
  where
    -- | Convert a partially applied expression to a syntax tree given a list of
    -- rendered missing arguments
    toTreeArgs :: [Tree String] -> expr a -> Tree String
    toTreeArgs args a = Node (renderSym a) args

instance (ToTree expr1, ToTree expr2) => ToTree (expr1 :+: expr2)
  where
    toTreeArgs args (InjL a) = toTreeArgs args a
    toTreeArgs args (InjR a) = toTreeArgs args a

-- | Show syntax tree using ASCII art
showAST :: ToTree dom => ASTF dom a -> String
showAST = drawTree . toTree renderSym

-- | Print syntax tree using ASCII art
drawAST :: ToTree dom => ASTF dom a -> IO ()
drawAST = putStrLn . showAST

