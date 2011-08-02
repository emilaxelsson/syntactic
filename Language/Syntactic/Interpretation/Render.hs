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
-- either of the methods 'render' and 'renderPart'.
class Render expr
  where
    -- | Render an expression as a 'String'
    render :: expr a -> String
    render = renderPart []

    -- | Render a partially applied constructor given a list of rendered missing
    -- arguments
    renderPart :: [String] -> expr a -> String
    renderPart []   a = render a
    renderPart args a = "(" ++ unwords (render a : args) ++ ")"

instance Render dom => Render (AST dom)
  where
    renderPart args (Symbol a) = renderPart args a
    renderPart args (f :$: a)  = renderPart (render a : args) f

instance Render dom => Show (AST dom a)
  where
    show = render

instance (Render expr1, Render expr2) => Render (expr1 :+: expr2)
  where
    renderPart args (InjectL a) = renderPart args a
    renderPart args (InjectR a) = renderPart args a

instance (Render expr1, Render expr2) => Show ((expr1 :+: expr2) a)
  where
    show = render

-- | Print an expression
printExpr :: Render expr => expr a -> IO ()
printExpr = putStrLn . render



class Render expr => ToTree expr
  where
    -- | Convert a partially applied constructor to a syntax tree given a list
    -- of rendered missing arguments
    toTreePart :: [Tree String] -> expr a -> Tree String
    toTreePart args a = Node (render a) args

instance ToTree dom => ToTree (AST dom)
  where
    toTreePart args (Symbol a) = toTreePart args a
    toTreePart args (f :$: a)  = toTreePart (toTree a : args) f

instance (ToTree expr1, ToTree expr2) => ToTree (expr1 :+: expr2)
  where
    toTreePart args (InjectL a) = toTreePart args a
    toTreePart args (InjectR a) = toTreePart args a

-- | Convert an expression to a syntax tree
toTree :: ToTree expr => expr a -> Tree String
toTree = toTreePart []

-- | Show syntax tree using ASCII art
showAST :: ToTree dom => AST dom a -> String
showAST = drawTree . toTree

-- | Print syntax tree using ASCII art
drawAST :: ToTree dom => AST dom a -> IO ()
drawAST = putStrLn . showAST

