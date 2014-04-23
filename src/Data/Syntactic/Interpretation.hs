{-# LANGUAGE TemplateHaskell #-}

-- | Equality and rendering of 'AST's

module Data.Syntactic.Interpretation
    ( -- * Equality
      Equality (..)
      -- * Rendering
    , Render (..)
    , renderArgsSmart
    , render
    , StringTree (..)
    , stringTree
    , showAST
    , drawAST
    , writeHtmlAST
      -- * Default interpretation
    , equalDefault
    , hashDefault
    , interpretationInstances
    ) where



import Data.Tree (Tree (..))
import Language.Haskell.TH

import Data.Hash (Hash, combine, hashInt)
import qualified Data.Hash as Hash
import Data.Tree.View

import Data.Syntactic.Syntax



----------------------------------------------------------------------------------------------------
-- * Equality
----------------------------------------------------------------------------------------------------

-- | Higher-kinded equality
class Equality e
  where
    -- | Higher-kinded equality
    --
    -- Comparing elements of different types is often needed when dealing with expressions with
    -- existentially quantified sub-terms.
    equal :: e a -> e b -> Bool

    -- | Higher-kinded hashing. Elements that are equal according to 'equal' must result in the same
    -- hash:
    --
    -- @equal a b  ==>  hash a == hash b@
    hash :: e a -> Hash

instance Equality sym => Equality (AST sym)
  where
    equal (Sym s1)   (Sym s2)   = equal s1 s2
    equal (s1 :$ a1) (s2 :$ a2) = equal s1 s2 && equal a1 a2
    equal _ _                   = False

    hash (Sym s)  = hashInt 0 `combine` hash s
    hash (s :$ a) = hashInt 1 `combine` hash s `combine` hash a

instance Equality sym => Eq (AST sym a)
  where
    (==) = equal

instance (Equality sym1, Equality sym2) => Equality (sym1 :+: sym2)
  where
    equal (InjL a) (InjL b) = equal a b
    equal (InjR a) (InjR b) = equal a b
    equal _ _               = False

    hash (InjL a) = hashInt 0 `combine` hash a
    hash (InjR a) = hashInt 1 `combine` hash a

instance (Equality sym1, Equality sym2) => Eq ((sym1 :+: sym2) a)
  where
    (==) = equal

instance Equality Empty
  where
    equal = error "equal: Empty"
    hash  = error "hash: Empty"



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

-- | Implementation of 'renderArgs' that handles infix operators
renderArgsSmart :: Render sym => [String] -> sym a -> String
renderArgsSmart []   sym = renderSym sym
renderArgsSmart args sym
    | isInfix   = "(" ++ unwords [a,op,b] ++ ")"
    | otherwise = "(" ++ unwords (name : args) ++ ")"
  where
    name  = renderSym sym
    [a,b] = args
    op    = init $ tail name
    isInfix
      =  not (null name)
      && head name == '('
      && last name == ')'
      && length args == 2

-- | Render an 'AST' as concrete syntax
render :: forall sym a. Render sym => ASTF sym a -> String
render = go []
  where
    go :: [String] -> AST sym sig -> String
    go args (Sym s)  = renderArgs args s
    go args (s :$ a) = go (render a : args) s

instance Render Empty
  where
    renderSym  = error "renderSym: Empty"
    renderArgs = error "renderArgs: Empty"

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

instance StringTree Empty

-- | Convert an 'AST' to a 'Tree' of strings
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

-- | Default implementation of 'equal'
equalDefault :: Render sym => sym a -> sym b -> Bool
equalDefault a b = renderSym a == renderSym b

-- | Default implementation of 'hash'
hashDefault :: Render sym => sym a -> Hash
hashDefault = Hash.hash . renderSym

-- | Derive instances for 'Equality' and 'StringTree'
interpretationInstances :: Name -> DecsQ
interpretationInstances n =
    [d|
        instance Equality $(typ) where
          equal = equalDefault
          hash  = hashDefault
        instance StringTree $(typ)
    |]
  where
    typ = conT n

