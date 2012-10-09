module Language.Syntactic.Interpretation.Render
    ( Render (..)
    , printExpr
    , ToTree (..)
    , showAST
    , drawAST
    ) where



import Data.Tree

import Language.Syntactic.Syntax



-- | Render an expression as concrete syntax. A complete instance must define
-- either of the methods 'render' and 'renderArgs'.
class Render expr
  where
    -- | Render an expression as a 'String'
    render :: expr a -> String
    render = renderArgs []

    -- | Render a partially applied expression given a list of rendered missing
    -- arguments
    renderArgs :: [String] -> expr a -> String
    renderArgs []   a = render a
    renderArgs args a = "(" ++ unwords (render a : args) ++ ")"

instance Render dom => Render (AST dom)
  where
    renderArgs args (Sym a)  = renderArgs args a
    renderArgs args (s :$ a) = renderArgs (render a : args) s

instance Render dom => Show (AST dom a)
  where
    show = render

instance (Render expr1, Render expr2) => Render (expr1 :+: expr2)
  where
    renderArgs args (InjL a) = renderArgs args a
    renderArgs args (InjR a) = renderArgs args a

instance (Render expr1, Render expr2) => Show ((expr1 :+: expr2) a)
  where
    show = render

-- | Print an expression
printExpr :: Render expr => expr a -> IO ()
printExpr = putStrLn . render



class Render expr => ToTree expr
  where
    -- | Convert a partially applied expression to a syntax tree given a list of
    -- rendered missing arguments
    toTreeArgs :: [Tree String] -> expr a -> Tree String
    toTreeArgs args a = Node (render a) args

instance ToTree dom => ToTree (AST dom)
  where
    toTreeArgs args (Sym a)  = toTreeArgs args a
    toTreeArgs args (s :$ a) = toTreeArgs (toTree a : args) s

instance (ToTree expr1, ToTree expr2) => ToTree (expr1 :+: expr2)
  where
    toTreeArgs args (InjL a) = toTreeArgs args a
    toTreeArgs args (InjR a) = toTreeArgs args a

-- | Convert an expression to a syntax tree
toTree :: ToTree expr => expr a -> Tree String
toTree = toTreeArgs []

-- | Show syntax tree using ASCII art
showAST :: ToTree dom => AST dom a -> String
showAST = drawTree . toTree

-- | Print syntax tree using ASCII art
drawAST :: ToTree dom => AST dom a -> IO ()
drawAST = putStrLn . showAST

