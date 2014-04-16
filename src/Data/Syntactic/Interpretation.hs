{-# LANGUAGE TemplateHaskell #-}

module Data.Syntactic.Interpretation
    ( -- * Equality
      Equality (..)
      -- * Rendering
    , Render (..)
    , render
    , StringTree (..)
    , stringTree
    , showAST
    , drawAST
    , writeHtmlAST
      -- * Default interpretation
    , Def (..)
    , Default (..)
    , equalDefault
    , exprHashDefault
    , renderSymDefault
    , renderArgsDefault
    , evaluateDefault
    , interpretationInstances
    ) where



import Data.Tree (Tree (..))
import Language.Haskell.TH
import Language.Haskell.TH.Quote

import Data.Hash
import Data.Tree.View

import Data.Syntactic.Syntax
import Data.Syntactic.Evaluation



----------------------------------------------------------------------------------------------------
-- * Equality
----------------------------------------------------------------------------------------------------

-- | Equality for expressions
class Equality expr
  where
    -- | Equality for expressions
    --
    -- Comparing expressions of different types is often needed when dealing
    -- with expressions with existentially quantified sub-terms.
    equal :: expr a -> expr b -> Bool

    -- | Computes a 'Hash' for an expression. Expressions that are equal
    -- according to 'equal' must result in the same hash:
    --
    -- @equal a b  ==>  exprHash a == exprHash b@
    exprHash :: expr a -> Hash


instance Equality sym => Equality (AST sym)
  where
    equal (Sym s1)   (Sym s2)   = equal s1 s2
    equal (s1 :$ a1) (s2 :$ a2) = equal s1 s2 && equal a1 a2
    equal _ _                   = False

    exprHash (Sym s)  = hashInt 0 `combine` exprHash s
    exprHash (s :$ a) = hashInt 1 `combine` exprHash s `combine` exprHash a

instance Equality sym => Eq (AST sym a)
  where
    (==) = equal

instance (Equality sym1, Equality sym2) => Equality (sym1 :+: sym2)
  where
    equal (InjL a) (InjL b) = equal a b
    equal (InjR a) (InjR b) = equal a b
    equal _ _               = False

    exprHash (InjL a) = hashInt 0 `combine` exprHash a
    exprHash (InjR a) = hashInt 1 `combine` exprHash a

instance (Equality expr1, Equality expr2) => Eq ((expr1 :+: expr2) a)
  where
    (==) = equal



----------------------------------------------------------------------------------------------------
-- * Rendering
----------------------------------------------------------------------------------------------------

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



----------------------------------------------------------------------------------------------------
-- * Default interpretation
----------------------------------------------------------------------------------------------------

-- | A representation of a syntactic construct as a 'String' and a semantic
-- function. It is not meant to be used as a syntactic symbol in an 'AST'. Its
-- only purpose is to provide the default implementations of functions like
-- `equal` via the `Default` class.
data Def a
  where
    Def
        :: { defaultName :: String
           , defaultEval :: Denotation a
           }
        -> Def a

instance Equality Def
  where
    equal (Def a _) (Def b _) = a==b
    exprHash (Def name _)     = hash name

instance Render Def
  where
    renderSym (Def name _) = name

    renderArgs [] (Def name _) = name
    renderArgs args (Def name _)
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

instance Eval Def
  where
    evaluate (Def _ a) = a

-- | Class of expressions that can be treated as constructs
class Default expr
  where
    defaultSym :: expr a -> Def a

-- | Default implementation of 'equal'
equalDefault :: Default expr => expr a -> expr b -> Bool
equalDefault a b = equal (defaultSym a) (defaultSym b)

-- | Default implementation of 'exprHash'
exprHashDefault :: Default expr => expr a -> Hash
exprHashDefault = exprHash . defaultSym

-- | Default implementation of 'renderSym'
renderSymDefault :: Default expr => expr a -> String
renderSymDefault = renderSym . defaultSym

-- | Default implementation of 'renderArgs'
renderArgsDefault :: Default expr => [String] -> expr a -> String
renderArgsDefault args = renderArgs args . defaultSym

-- | Default implementation of 'evaluate'
evaluateDefault :: Default expr => expr a -> Denotation a
evaluateDefault = evaluate . defaultSym

-- | Derive instances for interpretation classes ('Equality', 'Render', 'StringTree', 'Eval')
interpretationInstances :: Name -> DecsQ
interpretationInstances n =
    [d|
        instance Equality $(typ) where
          equal    = equalDefault
          exprHash = exprHashDefault
        instance Render $(typ) where
          renderSym  = renderSymDefault
          renderArgs = renderArgsDefault
        instance StringTree $(typ)
        instance Eval $(typ) where evaluate = evaluateDefault
    |]
  where
    typ = conT n

